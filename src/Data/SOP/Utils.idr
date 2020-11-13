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

-- ||| Creates a tuple of constraints from a a type-level function
-- ||| and a list of values.
-- |||
-- ||| ```idris example
-- ||| All Eq [Int,String,Char] = (Eq Int, Eq String, Eq Char)
-- ||| ```
-- public export
-- All : (f : k -> Type) -> (ks : List k) -> Type
-- All f []        = ()
-- All f (k :: ks) = (f k, All f ks)
