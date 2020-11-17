module Generics.SOP

import Decidable.Equality

import public Data.SOP.NP
import public Data.SOP.SOP
import public Data.SOP.Utils
import public Data.SOP.Interfaces

%default total

||| Interface for converting a data type from and to
||| its generic representation as a sum of products.
|||
||| Additional Idris coolness: This comes with proofs
||| that `from . to = id` and `to . from = id` and
||| thus, that `t` and `SOP code` are indeed isomorphic.
public export
interface Generic (t : Type) (code : List $ List Type) | t where
  ||| Converts the data type to its generic representation.
  from : (v : t) -> SOP I code

  ||| Converts the generic representation back to the original
  ||| value.
  to   : (v : SOP I code) -> t

  ||| Proof that `to . from = id`.
  fromToId : (v : t) -> to (from v) = v

  ||| Proof that `from . to = id`.
  toFromId : (v : SOP I code) -> from (to v) = v

export
fromInjective : Generic t code =>
                (0 x : t) -> (0 y : t) -> (from x = from y) -> x = y
fromInjective x y prf = rewrite sym $ fromToId y in lemma2
  where lemma1 : to {t = t} (from x) = to {t = t} (from y)
        lemma1 = cong to prf

        lemma2 : x = to {t = t} (from y)
        lemma2 = rewrite sym $ fromToId x in lemma1

--------------------------------------------------------------------------------
--          Generic Implementation Functions
--------------------------------------------------------------------------------

||| Default `(==)` implementation for data types with a `Generic`
||| instance.
public export
genEq : Generic t code => Eq (SOP I code) => t -> t -> Bool
genEq x y = from x == from y

||| Default `compare` implementation for data types with a `Generic`
||| instance.
public export
genCompare : Generic t code => Ord (SOP I code) => t -> t -> Ordering
genCompare x y = compare (from x) (from y)

||| Default `decEq` implementation for data types with a `Generic`
||| instance.
public export
genDecEq :  Generic t code => DecEq (SOP I code)
         => (x : t) -> (y : t) -> Dec (x = y)
genDecEq x y = case decEq (from x) (from y) of
                    (Yes prf)   => Yes $ fromInjective x y prf
                    (No contra) => No \h => contra (cong from h)

--------------------------------------------------------------------------------
--          Prelude Implementations
--------------------------------------------------------------------------------

-- I wrote the implementations below manually to get a feel for
-- their general structure before starting with deriving
-- them via elaborator reflection.

public export
Generic () [[]] where
  from () = Z []

  to (Z []) = ()
  to (S _) impossible

  fromToId () = Refl

  toFromId (Z []) = Refl

public export
Generic (a,b) [[a,b]] where
  from (a,b) = Z [a,b]

  to (Z [a,b]) = (a,b)
  to (S _) impossible

  fromToId (a,b) = Refl

  toFromId (Z [a,b]) = Refl

public export
Generic (LPair a b) [[a,b]] where
  from (a # b) = Z [a,b]

  to (Z [a,b]) = (a # b)
  to (S _) impossible

  fromToId (a # b) = Refl

  toFromId (Z [a, b]) = Refl

public export
Generic Void [] where
  from v impossible

  to v impossible

  fromToId v impossible

  toFromId v impossible

public export
Generic Nat [[],[Nat]] where
  from Z     = Z []
  from (S k) = S $ Z [k]

  to (Z [])      = Z
  to (S $ Z [k]) = S k

  fromToId 0     = Refl
  fromToId (S k) = Refl

  toFromId (Z [])      = Refl
  toFromId (S $ Z [k]) = Refl

public export
Generic (Maybe a) [[],[a]] where
  from Nothing  = Z []
  from (Just v) = S $ Z [v]

  to (Z [])      = Nothing
  to (S $ Z [v]) = Just v

  fromToId Nothing  = Refl
  fromToId (Just v) = Refl

  toFromId (Z [])      = Refl
  toFromId (S $ Z [v]) = Refl

public export
Generic (Dec t) [[t],[t -> Void]] where
  from (Yes t)  = Z [t]
  from (No f) = S $ Z [f]

  to (Z [t])     = Yes t
  to (S $ Z [f]) = No f

  fromToId (Yes t) = Refl
  fromToId (No f)  = Refl

  toFromId (Z [t])     = Refl
  toFromId (S $ Z [f]) = Refl

public export
Generic (Either a b ) [[a],[b]] where
  from (Left a)  = Z [a]
  from (Right b) = S $ Z [b]

  to (Z [a])     = Left a
  to (S $ Z [b]) = Right b

  fromToId (Left a)  = Refl
  fromToId (Right b) = Refl

  toFromId (Z [a])     = Refl
  toFromId (S $ Z [b]) = Refl

public export
Generic (List a) [[],[a,List a]] where
  from Nil      = Z []
  from (h :: t) = S $ Z [h,t]

  to (Z [])        = Nil
  to (S $ Z [h,t]) = h :: t

  fromToId Nil      = Refl
  fromToId (h :: t) = Refl

  toFromId (Z [])        = Refl
  toFromId (S $ Z [h,t]) = Refl

public export
Generic (Stream a) [[a, Inf (Stream a)]] where
  from (h :: t) = Z [h,t]

  to (Z [h,t])  = h :: t

  fromToId (h :: t) = Refl

  toFromId (Z [h,t]) = Refl
