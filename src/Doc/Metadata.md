## Metadata

```idris
module Doc.Metadata

import Generics.Derive
import Doc.Deriving

%language ElabReflection
```

```idris
export
data Spell = MkSpell Nat String

%runElab derive "Doc.Metadata.Spell" [Generic, Meta, Eq, Ord, DecEq, Show]

export
data Monster : Type where
  Goblin   : (hp : Int) -> (name : String) -> Monster
  Demon    : (hp : Int) -> (sp : Int) -> (spells : List Spell) -> Monster
  Skeleton : (hp : Int) -> (armor : Int) -> Monster

%runElab derive "Doc.Metadata.Monster" [Generic, Meta, Eq, Ord, DecEq, Show]

export
goblin : Monster
goblin = Goblin 87 "Garguzz"

export
demon : Monster
demon = Demon 530 120 [MkSpell 20 "Disintegrate"]
```

```idris
encodeCon : Encode (NP f ks) => ConInfo k ks -> NP f ks -> List String
encodeCon ci np = ci.conName.con :: encode np

encodeSOP :  (all : POP (Encode . f) kss)
          => TypeInfo k kss -> SOP f kss -> List String
encodeSOP {all = MkPOP _} (MkTypeInfo _ cons) =
  hconcat . hcliftA2 (Encode . NP f) encodeCon cons . unSOP

genEncode : Meta t code => POP Encode code => t -> List String
genEncode = encodeSOP (metaFor t) . from

EncodeVis : Visibility -> DeriveUtil -> InterfaceImpl
EncodeVis vis g = MkInterfaceImpl "Encode" vis []
                       `(mkEncode genEncode)
                       (implementationType `(Encode) g)

Encode' : DeriveUtil -> InterfaceImpl
Encode' = EncodeVis Public
```

```idris
-- Decodes a value prefixed by the given constructor's name
decodeCon : Decode a => ConInfo k ks -> (f : a -> b) -> Parser b
decodeCon ci f = string ci.conName.con *> map f decode

-- Tries to decode a sum type by first reading
-- a constructor's name before decoding the corresponding
-- n-ary product.
decodeSOP :  {kss : _} -> (all : POP (Decode . f) kss)
          => TypeInfo k kss -> Parser (SOP f kss)
decodeSOP {all = MkPOP _} (MkTypeInfo _ cons) =
  let is      = injections {f = NP' k f} {ks = kss}
      parsers = hcliftA2 (Decode . NP f) decodeCon cons is
   in MkSOP <$> hchoice parsers

-- Generic decoding function
genDecode : {code : _} -> Meta t code => POP Decode code => Parser t
genDecode = to <$> decodeSOP (metaFor t)

DecodeVis : Visibility -> DeriveUtil -> InterfaceImpl
DecodeVis vis g = MkInterfaceImpl "Decode" vis []
                       `(mkDecode genDecode)
                       (implementationType `(Decode) g)

Decode' : DeriveUtil -> InterfaceImpl
Decode' = DecodeVis Public

%runElab derive "Doc.Metadata.Spell" [Encode', Decode']

%runElab derive "Doc.Metadata.Monster" [Encode', Decode']

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
