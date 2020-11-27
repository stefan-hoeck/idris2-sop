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

%runElab derive "Doc.Metadata.Spell" [Encode']

%runElab derive "Doc.Metadata.Monster" [Encode']
```
