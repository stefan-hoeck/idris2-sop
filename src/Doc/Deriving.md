## Deriving Interface Implementations

A lot of ink has already been spilled over how we can use
generic representations to automatically derive interface
implementations, and I wrote several lengthy posts
about this topic for the
[idris2-elab-util](https://github.com/stefan-hoeck/idris2-elab-util)
package. Therefore, in this post, I'll only give examples about
how this library can be used to derive interface implementations
for a large group of data types automatically, without
going into the details about the underlying metaprogramming
machinery.

We start with the necessary imports and language extensions:

```idris
module Doc.Deriving

import Data.Strings
import Generics.Derive

%language ElabReflection
```

Note: At the moment, deriving interface implementations based on
constructor and argument names such as `Show` is not yet supported.
However, this is very high on my todo list, so I except it to be
available very soon.

### Product Types

Product types consist of a single constructor. Here is
an example of a spell in a role playing game (casting costs
plus the spell's name).

```idris
data Spell = MkSpell Nat String
```

Deriving the most common interface implementations is
straight forward (make sure to import `Generics.Derive`
and enable `%language ElabReflection`):

```idris
%runElab derive "Spell" [Generic, Eq, Ord, DecEq]
```

We can quicky write down some tests:

```idris
spellEq1 : MkSpell 12 "foo" == MkSpell 12 "foo" = True
spellEq1 = Refl

spellOrd1 : MkSpell 120 "" > MkSpell 12 "" = True
spellOrd1 = Refl
```

The library also supports additional forms of
product types.

Records:

```idris
record Dragon where
  constructor MkDragon
  name       : String
  hintPoints : Int
  spells     : List Spell
  treasure   : List String

%runElab derive "Dragon" [Generic, Eq, Ord, DecEq]
```

Parameterized types:

```idris
record BarbieDragon (treasureTpe : Type) (f : Type -> Type) where
  constructor MkBarbieDragon
  nameBD       : f String
  hintPointsBD : f Int
  spellsBD     : f $ List Spell
  treasureBD   : f $ List treasureTpe

%runElab derive "BarbieDragon" [Generic, Eq, Ord, DecEq]
```

Recursive types:

```idris
record Hero where
  constructor MkHero
  title     : String
  hp        : Int
  equipment : List String
  allies    : List Hero

%runElab derive "Hero" [Generic, Eq, Ord, DecEq]
```

Some implementations like the ones for `Semigroup` or `Monoid` can
only be derived for product types:

```idris
record Employees where
  constructor MkEmployees
  names     : List String
  addresses : List String
  salaries  : List Double

%runElab derive "Employees" [Generic, Eq, Ord, Semigroup, Monoid]

tableTest : MkEmployees [] [] [] = neutral {ty = Employees}
tableTest = Refl

tableTest2 : MkEmployees ["a"] [] [1] <+> MkEmployees ["a"] ["b"] [2,3] =
             MkEmployees ["a","a"] ["b"] [1,2,3]
tableTest2 = Refl
```

### Sum Types

Sum types have more than one constructor but other than that,
deriving instances for them is just as easy as for products:

```idris
data Monster : Type where
  Goblin   : (hp : Int) -> (name : String) -> Monster
  Demon    : (hp : Int) -> (sp : Int) -> (spells : List Spell) -> Monster
  Skeleton : (hp : Int) -> (armor : Int) -> Monster

%runElab derive "Monster" [Generic, Eq, Ord, DecEq]
```

Likewise, parameterized and inductive types are supported
as well:

```idris
data Treasure : Type where
  Coins  : (value : Nat) -> Treasure
  Jewels : (types : List (Nat,String)) -> Treasure
  Chest  : (content : List Treasure) -> Treasure

%runElab derive "Treasure" [Generic, Eq, Ord, DecEq]
```

### Deriving Implementations for your own Interfaces

As a fully worked out example, in this part we are going to
implement basic interfaces
for encoding and decoding values to and from lists of string tokens.
These tokens could for instance represent the fields on a single line
of a .csv file.

To keep things simple, we quickly write our own very basic
parser type.

#### A Simple Parser for Decoding Lists of Strings

```idris
||| Tries to convert parts of a list of string tokens
||| returning either the result plus the remainder
||| of the list or the remainder of the list where parsing failed.
public export
record Parser (t : Type) where
  constructor MkParser
  run : List String -> Either (List String) (t, List String)

public export
Functor Parser where
  map f pa = MkParser \ts => do (a,ts') <- pa.run ts
                                pure (f a, ts')

public export
Applicative Parser where
  pure a = MkParser \ts => Right (a,ts)

  pf <*> pa = MkParser \ts => do (f, ts' ) <- pf.run ts
                                 (a, ts'') <- pa.run ts'
                                 pure (f a, ts'')

public export
Monad Parser where
  pa >>= f = MkParser \ts => do (a, ts' ) <- pa.run ts
                                (f a).run ts'

public export
Alternative Parser where
  empty = MkParser Left

  p1 <|> p2 = MkParser \ts => case p1.run ts of
                                   Left _ => p2.run ts
                                   res    => res

||| Returns the next string token, failing if
||| the list of tokens is empty.
public export
next : Parser String
next = MkParser \ts => case ts of
                            []     => Left []
                            (h::t) => Right (h,t)

||| Succeeds if the next token matches exactly the
||| given String.
public export
string : String -> Parser ()
string s = next >>= guard . (s ==)

||| Maps a partial function over the result
||| of a parser. This fails, if the function returns
||| `Nothing`-
public export
mapMaybe : (a -> Maybe b) -> Parser a -> Parser b
mapMaybe f = (>>= maybe empty pure . f)

||| Tries to parse the given number of values.
public export
repeat : Parser a -> Nat -> Parser (List a)
repeat _ 0     = pure []
repeat p (S n) = [| p :: repeat p n |]

||| Runs a parser against a list of string tokens.
||| Fails if not the whole list is consumed.
public export
parse : Parser t -> List String -> Either (List String) t
parse p ts = case p.run ts of
                  Right (t,[]) => Right t
                  Right (_,ts) => Left ts
                  Left ts      => Left ts
```

#### Generically derived Encoders

Next, we provide some primitives for encoding values to
lists of string tokens:

```idris
public export
interface Encode t where
  encode : t -> List String

public export
Encode Int where encode = pure . show

public export
Encode Double where encode = pure . show

public export
Encode Bool where encode = pure . show

public export
Encode Nat where encode = pure . show . cast {to = Integer}

public export
Encode String where encode = pure

||| Encoded lists are prefixed with an ecoding of
||| the number of elements
public export
Encode a => Encode (List a) where
  encode as = encode (length as) ++ concatMap encode as
```

Now, we need an instance for products. As a prerequisite, we
require every element in an n-ary product to have an
instance of `Encode`. We can use an implicit value of
type `NP (Encode . f) ks` to formulate this prerequisite.
This allows us to either implement `encode` by pattern matching
on the product we'd like to encode or by using some
of the combinators provided by this library. `hcmap` followed
by `hconcat` will do the job:

```idris
public export
NP (Encode . f) ks => Encode (NP f ks) where
  encode = hconcat . hcmap (Encode . f) encode

```

The same goes for n-ary sums. Here, as a precodition, we only
accept single constructor sums, otherwise we'd had
to somehow encode the constructor as a prefix to the remainer
of the list. This can be done by using the `SingletonList`
predicate from `Data.SOP.Utils`.
Otherwise, the implementation uses exactly the same combinators
as the one for `NP`.


```idris
NP (Encode . f) ks => SingletonList ks => Encode (NS f ks) where
  encode = hconcat . hcmap (Encode . f) encode
```

From the above, we can directly derive instances
for products of products and sums of products.

```idris
public export
POP (Encode . f) kss => Encode (POP f kss) where
  encode (MkPOP nps) = encode nps

POP (Encode . f) kss => SingletonList kss => Encode (SOP f kss) where
  encode (MkSOP v) = encode v
```

Note that in the case of a sum type, we still need the corresponding
product type as a witnesses that we have interface implementations
for all possible fields of the sum.

Next, we define a generic version of `encode`:

```idris
genEncode :  Generic t code
          => POP Encode code
          => SingletonList code
          => t -> List String
genEncode = encode . from
```

Just as we like it: The type declaration takes up far more space
than the actual implementation. :-)

With this, we can already write derived implementations manually:

```idris
Encode Spell where encode = genEncode

||| The result can't be reduced any further, since `show` and
||| `cast` of primitives is involved.
encodeSpellTest : encode (MkSpell 10 "foo") =
                  [show (cast {from = Nat} {to = Integer} 10), "foo"]
encodeSpellTest = Refl
```

In order to make the interface available to function `derive`,
we have to write a minimal amount of reflection code:

```idris
||| It is important that this is publicly exported, in case
||| we later on want to proof the correctnes of implementations.
public export
mkEncode : (t -> List String) -> Encode t
mkEncode = %runElab check (var $ singleCon "Encode")

||| Derives an `Encode` implementation for the given data type
||| and visibility.
EncodeVis : Visibility -> DeriveUtil -> InterfaceImpl
EncodeVis vis g = MkInterfaceImpl "Encode" vis []
                       `(mkEncode genEncode)
                       (implementationType `(Encode) g)

||| Alias for `EncodeVis Public`.
Encode' : DeriveUtil -> InterfaceImpl
Encode' = EncodeVis Public
```

Let's encode us some dragons:

```idris
%runElab derive "Dragon" [Encode']
```

#### Generically derived Decoders

Deriving decoders is only slightly more involved. First, we
need again some primitives:

```idris
public export
interface Decode t where
  decode : Parser t

public export
Decode Int where decode = mapMaybe parseInteger next

public export
Decode Double where decode = mapMaybe parseDouble next

public export
Decode Bool where
  decode = mapMaybe parseBool next
    where parseBool : String -> Maybe Bool
          parseBool "False" = Just False
          parseBool "True"  = Just True
          parseBool _       = Nothing

public export
Decode Nat where decode = mapMaybe parsePositive next

public export
Decode String where decode = next

||| First, the number of elements is decoded, followed
||| by a repeated application of the element Decoder.
public export
Decode a => Decode (List a) where
  decode = decode >>= repeat decode
```

Now come the decoders for n-ary products.
We can use `hcpure` and `hsequence` for this:

```idris
public export
NP (Decode . f) ks => Decode (NP f ks) where
  decode = hsequence $ hcpure (Decode . f) decode
```

For sums, we once again allow only sums representing
types with a single constructor. In this
case we need to pattern match on the implicitly available `Decode` instance
to make it available when decoding the inner
value:

```idris
(decs : NP (Decode . f) ks) => SingletonList ks => Decode (NS f ks) where
  decode {decs = _ :: _ } = map Z decode
```

Finally, the trivial versions for `POP` and `SOP`:

```idris
public export
POP (Decode . f) kss => Decode (POP f kss) where
  decode = map MkPOP decode

POP (Decode . f) kss => SingletonList kss => Decode (SOP f kss) where
  decode = map MkSOP decode
```

And again, we provide a generic version of `decode`:

```idris
genDecode :  Generic t code
          => POP Decode code
          => SingletonList code
          => Parser t
genDecode = map to decode
```

Finally, the necessary reflection code:

```idris
public export
mkDecode : Parser t -> Decode t
mkDecode = %runElab check (var $ singleCon "Decode")

||| Derives a `Decode` implementation for the given data type
||| and visibility.
DecodeVis : Visibility -> DeriveUtil -> InterfaceImpl
DecodeVis vis g = MkInterfaceImpl "Decode" vis []
                       `(mkDecode genDecode)
                       (implementationType `(Decode) g)

||| Alias for `DecodeVis Public`.
Decode' : DeriveUtil -> InterfaceImpl
Decode' = DecodeVis Public
```

Let's decode us some dragons:

```idris
%runElab derive "Spell" [Decode']

%runElab derive "Dragon" [Decode']
```

In order to play around with this in the REPL, we need access
to a dragon:

```idris
public export
gorgar : Dragon
gorgar = MkDragon "GORGAR" 15000
           [MkSpell 100 "Fireball", MkSpell 20 "Invisibility"]
           ["Mail of Mithril", "1'000 gold coins"]

export
printGorgar : IO ()
printGorgar = printLn $ encode gorgar

export
testDecodingGorgar : IO ()
testDecodingGorgar = printLn $ Right gorgar == parse decode (encode gorgar)
```

### Conclusion

This post demonstrated the most important aspects of deriving
interface implementations automatically from generic representations
of data types as well as the most basic pieces of reflection
code necessary to make intefaces available to `derive`.
For a much more thorough introduction to the concepts and code
behind `derive`, see the tutorials on *Generics* at
the [idris2-elab-util](https://github.com/stefan-hoeck/idris2-elab-util)
package.

In the [next part](Metadata.md), we are going to enhance our
encoders and decoders to properly support sum types. For this,
we will need access to a data type's metadata like
constructor and argument names.
