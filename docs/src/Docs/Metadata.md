# Metadata

In the [last part](Deriving.md) of the tutorial, we experimented with
automatically deriving different interface implementations. Those
examples could be derived directly from a data type's type-level
code without the need for additional information.

For some interfaces like `Show`, however, this is not enough: In order
to derive a `Show` instance, we need to know about constructor names and
possibly record field names. In this part of the tutorial we learn how to
get access to those and how to make use of this information
to enhance our own `Encoder` and `Decoder` interfaces from the
last part.

```idris
module Docs.Metadata

import Generics.Derive
import Docs.Deriving

%language ElabReflection
```

## `Meta`: An Interface for Metadata

Getting access to a data type's metadata is as simple as deriving
its `Meta` interface (from module `Generics.Meta`). This gives us access
to functions `meta` and `metaFor`, both of which return a `TypeInfo`
record, wrapping a product of `ConInfo` values.
Like `SOP`, `TypeInfo` is indexed over a list of lists of values to
match the structure of the generic code of a data type.

Before we learn how to use metadata to write our own interface
implementations, here are two data types with automatically
derived `Meta` and `Show` implementations (we have to use fully
qualified names, because module `Docs.Deriving` contains private data types
with identical names, which seems to confuse Idris):

```idris
export
data Spell = MkSpell Nat String

%runElab derive "Docs.Metadata.Spell" [Generic, Meta, Eq, Ord, DecEq, Show]

export
data Monster : Type where
  Goblin   : (hp : Int) -> (name : String) -> Monster
  Demon    : (hp : Int) -> (sp : Int) -> (spells : List Spell) -> Monster
  Skeleton : (hp : Int) -> (armor : Int) -> Monster

%runElab derive "Docs.Metadata.Monster" [Generic, Meta, Eq, Ord, Show]
```

## An `Encoder` for Sum Types

So far, we only supported the deriving of decoders for product
types. We'd like to also support sum types, by prefixing encodings
with the corresponding constructor's name:

```idris
encodeCon : Encode (NP f ks) => ConInfo ks -> NP f ks -> List String
encodeCon ci np = ci.conName :: encode np
```

Since a type's constructors are wrapped in an `NP` parameterized
by the same type level list as its generic representation,
we can use the usual SOP combinators to generate an
encoding for a `SOP` value. As can be guessed from the type of `encodeCon`
we can use `hcliftA2` followed by `hconcat`:

```idris
genEncode : Meta t code => (all : POP Encode code) => t -> List String
genEncode {all = MkPOP _} = encodeSOP (metaFor t) . from
  where encodeSOP : TypeInfo code -> SOP I code -> List String
        encodeSOP (MkTypeInfo _ _ cons) =
          hconcat . hcliftA2 (Encode . NP I) encodeCon cons . unSOP
```

The functions to be used in `derive` are verbatim copies of the
ones used in the last post, but they call a different version
of `genEncode`, therefore we have to include them here:

```idris
Encode' : List Name -> ParamTypeInfo -> Res (List TopLevel)
Encode' _ p =
  let nm := implName p "Encode"
      cl := patClause (var nm) `(MkEncode genEncode)
   in Right [TL (interfaceHint Public nm (implType "Encode" p)) (def nm [cl])]
```

## Decoding Sum Types: A Use Case for `injections`

We will need a new SOP technique for decoding sum types.
But first, decoding a single constructor seems to be straight
forward: We read the expected constructor name before
decoding the arguments.
However, as can be seen in the implementation of `decodeCon`
we somehow need to convert the decoded n-ary sum to a `SOP`
value by applying the correct sequence of `S` and `Z` constructors:

```idris
decodeCon :  forall ks . Decode (NP f ks)
          => ConInfo ks -> (toSOP : NP f ks -> SOP f kss) -> Parser (SOP f kss)
decodeCon ci toSOP = string ci.conName *> map toSOP decode
```

Function `toSOP` is called an *injection* into the n-ary sum. Module *Data.SOP*
provides function `injectionsSOP`, returning an n-ary product of all
injections from n-ary products into a sum of products parameterized over
the given typelevel list of lists. In order to combine the resulting
n-ary product of parsers, we use function `hchoice` making use of
the `Alternative` instance of `Parser`:

```idris
-- Generic decoding function
genDecode : {code : _} -> Meta t code => (all : POP Decode code) => Parser t
genDecode {all = MkPOP _} = to <$> decodeSOP (metaFor t)
  where decodeSOP : TypeInfo code -> Parser (SOP I code)
        decodeSOP (MkTypeInfo _ _ cons) =
          hchoice $ hcliftA2 (Decode . NP I) decodeCon cons injectionsSOP
```

Again, the functions to be used in `derive` are verbatim copies of the
ones used in the last post:


```idris
Decode' : List Name -> ParamTypeInfo -> Res (List TopLevel)
Decode' _ p =
  let nm := implName p "Decode"
      cl := patClause (var nm) `(MkDecode genDecode)
   in Right [TL (interfaceHint Public nm (implType "Decode" p)) (def nm [cl])]
```

We can now derive encoders and decoders for `Monster`s and
test them at the REPL:

```idris
%runElab derive "Docs.Metadata.Spell" [Encode', Decode']

%runElab derive "Docs.Metadata.Monster" [Encode', Decode']

export
demon : Monster
demon = Demon { hp = 530
              , sp = 120
              , spells = [MkSpell 40 "Disintegrate", MkSpell 10 "Utterdark"]
              }

export
encDemon : List String
encDemon = encode demon

export
decDemon : Either (List String) Monster
decDemon = parse decode encDemon

export
printDecDemon : IO ()
printDecDemon = printLn decDemon
```

## Conclusion

Again, the SOP approach provides powerful abstraction to write
generic interface implementations. This post completes the part
about deriving interface implementations. Still, there are other
possibilities and techniques of this library to explore, for
instance the ability to provide automatically
generated lenses.

<!-- vi: filetype=idris2:syntax=markdown
-->
