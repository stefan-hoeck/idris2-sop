module Generics.SOP

import Decidable.Equality

import public Data.List.Elem
import public Data.SOP

%default total

||| Interface for converting a data type from and to
||| its generic representation as a sum of products.
|||
||| Additional Idris coolness: This comes with proofs
||| that `from . to = id` and `to . from = id` and
||| thus, that `t` and `SOP code` are indeed isomorphic.
public export
interface Generic (0 t : Type) (0 code : List $ List Type) | t where
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

public export
0 Code : (t : Type) -> Generic t code => List $ List Type
Code _ = code

||| Tries to extract the arguments of a single constructor
||| from a value's generic representation.
public export
genExtract :  (0 ts : List Type)
           -> (v : t)
           -> Generic t code
           => {auto prf : Elem ts code}
           -> Maybe (NP I ts)
genExtract ts v = extractSOP ts $ from v

||| Tries to extract the value of a single one argument
||| constructor from a value's generic representation.
public export
genExtract1 :  (0 t' : Type)
            -> (v : t)
            -> Generic t code
            => {auto prf : Elem [t'] code}
            -> Maybe t'
genExtract1 t' v = hd <$> genExtract [t'] v

--------------------------------------------------------------------------------
--          Generic Implementation Functions
--------------------------------------------------------------------------------

||| Default `(==)` implementation for data types with a `Generic`
||| instance.
public export
genEq : Generic t code => POP Eq code => t -> t -> Bool
genEq x y = from x == from y

||| Default `compare` implementation for data types with a `Generic`
||| instance.
public export
genCompare : Generic t code => POP Ord code => t -> t -> Ordering
genCompare x y = compare (from x) (from y)

||| Default `decEq` implementation for data types with a `Generic`
||| instance.
public export
genDecEq :  Generic t code => POP DecEq code
         => (x : t) -> (y : t) -> Dec (x = y)
genDecEq x y = case decEq (from x) (from y) of
                    (Yes prf)   => Yes $ fromInjective x y prf
                    (No contra) => No \h => contra (cong from h)

||| Default `(<+>)` implementation for data types with a `Generic`
||| instance.
public export
genAppend :  Generic t [ts]
          => POP Semigroup [ts]
          => t -> t -> t
genAppend x y = to $ from x <+> from y

||| Default `neutral` implementation for data types with a `Generic`
||| instance.
public export
genNeutral :  Generic t [ts] => POP Monoid [ts] => t
genNeutral = to neutral

--------------------------------------------------------------------------------
--          Prelude Implementations
--------------------------------------------------------------------------------

-- I wrote the implementations below manually to get a feel for
-- their general structure before starting with deriving
-- them via elaborator reflection.

public export
Generic () [[]] where
  from () = MkSOP $ Z []

  to (MkSOP $ Z []) = ()
  to (MkSOP $ S _) impossible

  fromToId () = Refl

  toFromId (MkSOP $ Z []) = Refl

public export
Generic (a,b) [[a,b]] where
  from (a,b) = MkSOP $ Z [a,b]

  to (MkSOP $ Z [a,b]) = (a,b)
  to (MkSOP $ S _) impossible

  fromToId (a,b) = Refl

  toFromId (MkSOP $ Z [a,b]) = Refl

public export
Generic (LPair a b) [[a,b]] where
  from (a # b) = MkSOP $ Z [a,b]

  to (MkSOP $ Z [a,b]) = (a # b)
  to (MkSOP $ S _) impossible

  fromToId (a # b) = Refl

  toFromId (MkSOP $ Z [a, b]) = Refl

public export
Generic Void [] where
  from v impossible

  to (MkSOP v) impossible

  fromToId v impossible

  toFromId (MkSOP v) impossible

public export
Generic Nat [[],[Nat]] where
  from Z     = MkSOP $ Z []
  from (S k) = MkSOP $ S $ Z [k]

  to (MkSOP $ Z [])      = Z
  to (MkSOP $ S $ Z [k]) = S k

  fromToId 0     = Refl
  fromToId (S k) = Refl

  toFromId (MkSOP $ Z [])      = Refl
  toFromId (MkSOP $ S $ Z [k]) = Refl

public export
Generic (Maybe a) [[],[a]] where
  from Nothing  = MkSOP $ Z []
  from (Just v) = MkSOP $ S $ Z [v]

  to (MkSOP $ Z [])      = Nothing
  to (MkSOP $ S $ Z [v]) = Just v

  fromToId Nothing  = Refl
  fromToId (Just v) = Refl

  toFromId (MkSOP $ Z [])      = Refl
  toFromId (MkSOP $ S $ Z [v]) = Refl

public export
Generic (Dec t) [[t],[t -> Void]] where
  from (Yes t)  = MkSOP $ Z [t]
  from (No f) = MkSOP $ S $ Z [f]

  to (MkSOP $ Z [t])     = Yes t
  to (MkSOP $ S $ Z [f]) = No f

  fromToId (Yes t) = Refl
  fromToId (No f)  = Refl

  toFromId (MkSOP $ Z [t])     = Refl
  toFromId (MkSOP $ S $ Z [f]) = Refl

public export
Generic (Either a b ) [[a],[b]] where
  from (Left a)  = MkSOP $ Z [a]
  from (Right b) = MkSOP $ S $ Z [b]

  to (MkSOP $ Z [a])     = Left a
  to (MkSOP $ S $ Z [b]) = Right b

  fromToId (Left a)  = Refl
  fromToId (Right b) = Refl

  toFromId (MkSOP $ Z [a])     = Refl
  toFromId (MkSOP $ S $ Z [b]) = Refl

public export
Generic (List a) [[],[a,List a]] where
  from Nil      = MkSOP $ Z []
  from (h :: t) = MkSOP $ S $ Z [h,t]

  to (MkSOP $ Z [])        = Nil
  to (MkSOP $ S $ Z [h,t]) = h :: t

  fromToId Nil      = Refl
  fromToId (h :: t) = Refl

  toFromId (MkSOP $ Z [])        = Refl
  toFromId (MkSOP $ S $ Z [h,t]) = Refl

public export
Generic (Stream a) [[a, Inf (Stream a)]] where
  from (h :: t) = MkSOP $ Z [h,t]

  to (MkSOP $ Z [h,t])  = h :: t

  fromToId (h :: t) = Refl

  toFromId (MkSOP $ Z [h,t]) = Refl
