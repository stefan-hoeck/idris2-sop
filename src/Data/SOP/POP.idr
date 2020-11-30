module Data.SOP.POP

import Data.SOP.Utils
import Data.SOP.Interfaces
import Data.SOP.NP

import Decidable.Equality

%default total

||| A product of products.
|||
||| The elements of the inner products are
||| applications of the parameter f. The type POP is indexed by the list of lists
||| that determines the lengths of both the outer and all the inner products, as
||| well as the types of all the elements of the inner products.
|||
||| A POP is reminiscent of a two-dimensional table (but the inner lists can all be
||| of different length). In the context of the SOP approach to
||| generic programming, a POP is useful to represent information
||| that is available for all arguments of all constructors of a datatype.
public export
data POP' : (k : Type) -> (f : k -> Type) -> (kss : List (List k)) -> Type where
  MkPOP : NP' (List k) (NP' k f) kss -> POP' k f kss

||| Type alias for `POP'` with type parameter `k` being
||| implicit. This reflects the kind-polymorphic data type
||| in Haskell.
public export
POP : {k : Type} -> (f : k -> Type) -> (kss : List (List k)) -> Type
POP = POP' k

public export %inline
unPOP : POP' k f kss -> NP' (List k) (NP' k f) kss
unPOP (MkPOP np) = np

--------------------------------------------------------------------------------
--          Specialized Interface Functions
--------------------------------------------------------------------------------

||| Specialiced version of `hmap`
public export
mapPOP : (fun : forall a . f a -> g a) -> POP f kss -> POP g kss
mapPOP fun = MkPOP . mapNP (\p => mapNP fun p) . unPOP

||| Specialization of `hpure`.
public export
purePOP : {kss : _} -> (forall a . f a) -> POP f kss
purePOP {kss = []}     fun = MkPOP []
purePOP {kss = _ :: _} fun = let (MkPOP nps) = purePOP fun
                              in MkPOP $ pureNP fun :: nps

||| Specialization of `hap`.
public export
hapPOP : POP (\a => f a -> g a) kss -> POP f kss -> POP g kss
hapPOP (MkPOP fs) = MkPOP . hliftA2 (\p => hapNP p) fs . unPOP

||| Specialization of `hfoldl`
public export
foldlPOP : (fun : acc -> elem -> acc) -> acc -> POP (K elem) kss -> acc
foldlPOP _   acc (MkPOP [])     = acc
foldlPOP fun acc (MkPOP (h::t)) = foldlPOP fun (foldlNP fun acc h) (MkPOP t)

||| Specialization of `hfoldr`
public export
foldrPOP : (fun : elem -> Lazy acc -> acc) -> Lazy acc -> POP (K elem) kss -> acc
foldrPOP _   acc (MkPOP [])     = acc
foldrPOP fun acc (MkPOP (h::t)) = foldrNP fun (foldrPOP fun acc (MkPOP t)) h

||| Specialization of `hsequence`
public export
sequencePOP : Applicative g => POP (\a => g (f a)) kss -> g (POP f kss)
sequencePOP = map MkPOP . sequenceNP . mapNP (\p => sequenceNP p) . unPOP

--------------------------------------------------------------------------------
--          Interface Conversions
--------------------------------------------------------------------------------

||| This is needed to implement `Ord` below.
public export %hint
ordToEqPOP :  POP (Ord . f) kss -> POP (Eq . f) kss
ordToEqPOP = mapPOP (\_ => materialize Eq)

||| This is needed to implement `Monoid` below.
public export %hint
monoidToSemigroupPOP : POP (Monoid . f) kss -> POP (Semigroup . f) kss
monoidToSemigroupPOP = mapPOP (\_ => materialize Semigroup)

||| Converts a POP of constraints to an n-ary sum
||| holding constrains about the inner n-ary sum.
|||
||| Example : POP Eq typess -> NP (Eq . NP I) typess
|||
||| In the example above, we convert a POP of `Eq` instances
||| into an n-ary sum of Eq instances of the inner products.
||| This allows us to for instance implent `Eq (POP f kss) ` below
||| via a direct call to (==) specialized to Eq (NP (NP f) kss).
public export %hint
popToNP :  POP' k (c . f) kss
        -> {auto prf : forall ks . NP' k (c . f) ks => c (NP' k f ks)}
        -> NP' (List k) (c . NP' k f) kss
popToNP (MkPOP nps) = hmap (\_ => prf) nps

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export %inline
HPure k (List $ List k) (POP' k) where hpure  = purePOP

public export %inline
HFunctor k (List $ List k) (POP' k) where hmap  = mapPOP

public export %inline
HAp k (List $ List k) (POP' k) (POP' k) where hap = hapPOP

public export %inline
HFold k (List $ List k) (POP' k) where
  hfoldl = foldlPOP
  hfoldr = foldrPOP

public export %inline
HSequence k (List $ List k) (POP' k) where hsequence = sequencePOP

public export
POP (Eq . f) kss => Eq (POP' k f kss) where
  MkPOP a == MkPOP b = a == b

public export
POP (Ord . f) kss => Ord (POP' k f kss) where
  compare (MkPOP a) (MkPOP b) = compare a b

public export
POP (Semigroup . f) kss => Semigroup (POP' k f kss) where
  MkPOP a <+> MkPOP b = MkPOP $ a <+> b

public export
POP (Monoid . f) kss => Monoid (POP' k f kss) where
  neutral = MkPOP neutral

private
mkPOPInjective : MkPOP a = MkPOP b -> a = b
mkPOPInjective Refl = Refl

public export
POP (DecEq . f) kss => DecEq (POP' k f kss) where
  decEq (MkPOP a) (MkPOP b) with (decEq a b)
    decEq (MkPOP a) (MkPOP a) | Yes Refl   = Yes $ cong MkPOP Refl
    decEq (MkPOP a) (MkPOP b) | No  contra = No (contra . mkPOPInjective)
