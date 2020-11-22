module Data.SOP.Utils

%default total

||| Type-level identity function.
public export
I : Type -> Type
I v = v

||| Type-level constant function.
public export
K : Type -> k -> Type
K t _ = t

--------------------------------------------------------------------------------
--          Interface Conversions
--------------------------------------------------------------------------------

||| This is needed in interface implementations in the library
||| for the following reasons:
|||
||| a) Interface resolution for the following implementation of `Ord`
|||    was horribly slow (several seconds for NP values with six
|||    values, no longer terminating for more values):
|||
||| ```idris
||| Eq (f t) => Eq (NP' k f ks) => Eq (NP' k f (t :: ks)) where
|||   (v :: vs) == (w :: ws) = v == w && vs == ws
||| 
||| Ord (f t) => Ord (NP' k f ks) => Ord (NP' k f (t :: ks)) where
|||   compare (v :: vs) (w :: ws) = compare v w <+> compare vs ws
||| ```
|||
||| b) I then tried the following approach:
|||
||| ```idris
||| All : (f : k -> Type) -> List k -> Type
||| All _ [] = ()
||| All f (t::ts) = (f t, All f ts)
|||
||| All (Eq . f) ks => Eq (NP' k f ks) where
|||
||| All (Eq . f) ks => All (Ord . f) ks => Ord (NP' k f ks) where
||| ```
|||
||| Resolution was now much faster, but I got stuck on profing
||| laws about interface implementations. Hence this new approach.
public export
ordToEq : Ord a -> Eq a
ordToEq o = eq {b = a}
  where eq : (e : Eq b) => Eq b
        eq {e} = e

public export
monoidToSemigroup : Monoid a -> Semigroup a
monoidToSemigroup m = sem {b = a}
  where sem : (s : Semigroup b) => Semigroup b
        sem {s} = s
