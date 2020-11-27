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
encodeSOP :  (all : POP' k (Encode . f) kss)
          => TypeInfo k kss -> SOP' k f kss -> List String
encodeSOP {all = MkPOP _} (MkTypeInfo _ cons) (MkSOP ns) =
  hconcat $ hcliftA2 (Encode . NP' k f) doEncode cons ns
    where doEncode :  Encode (NP' k f ks)
                   => ConInfo k ks -> NP' k f ks -> List String
          doEncode ci np = ci.conName.con :: encode np

genEncode : Meta t code => POP Encode code => t -> List String
genEncode = encodeSOP (metaFor t) . from

||| Derives an `Encode` implementation for the given data type
||| and visibility.
EncodeVis : Visibility -> DeriveUtil -> InterfaceImpl
EncodeVis vis g = MkInterfaceImpl "Encode" vis []
                       `(mkEncode genEncode)
                       (implementationType `(Encode) g)

||| Alias for `EncodeVis Public`.
Encode' : DeriveUtil -> InterfaceImpl
Encode' = EncodeVis Public

%runElab derive "Doc.Metadata.Spell" [Encode']

%runElab derive "Doc.Metadata.Monster" [Encode']
```
