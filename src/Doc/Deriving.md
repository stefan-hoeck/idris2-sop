## Deriving Interface Implementations

A lot of ink has alreday been spilled over how we can use
generic representations to automatically derive interface
implementations, and I worte several lengthy posts
about this topic for the
[idris2-elab-util](https://github.com/stefan-hoeck/idris2-elab-util)
package. Therefore, in this post, I'll only give examples about
how this library can be used to derive interface implementations
for a large group of data types automatically.

We start with the necessary imports and language extensions:

```idris
module Doc.Deriving

import Decidable.Equality
import Generics.Derive

%language ElabReflection
```

Note: At the moment, deriving interface implementations based on
constructor and argument names such as `Show` is not yet supported.
However, this is very high on my todo list, so I except it to be
available very soon.

### Product Types

Product types constist of a single constructor. Here is
an example of a spell in a role playing game (casting costs
plus the spell's name):

```idris
data Spell = MkSpell Nat String

%runElab derive "Spell" [Generic, Eq, Ord, DecEq]
```

We can quicky write down some tests:

```idris
spellEq1 : MkSpell 12 "foo" == MkSpell 12 "foo" = True
spellEq1 = Refl

spellOrd1 : MkSpell 120 "" > MkSpell 12 "" = True
spellOrd1 = Refl
```

The library also supports additional types of
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
record DragonF (treasureTpe : Type) (f : Type -> Type) where
  constructor MkDragonF
  nameF       : f String
  hintPointsF : f Int
  spellsF     : f $ List Spell
  treasureF   : f $ List treasureTpe

%runElab derive "DragonF" [Generic, Eq, Ord, DecEq]
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

### Sum Types

To be added.

### Deriving your own Interfaces

To be added.
