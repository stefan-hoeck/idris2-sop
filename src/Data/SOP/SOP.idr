module Data.SOP.SOP

import Data.SOP.NP
import Data.SOP.NS
import Data.SOP.POP
import Data.SOP.Utils
import Data.SOP.Interfaces

import Decidable.Equality

%default total

||| A sum of products.
|||
||| Unlike in the Haskell version, not using a Newtype here allows us
||| to overload the costructor names of NS'.
||| The elements of the (inner) products
||| are applications of the parameter f. The type SOP' is indexed by the list of
||| lists that determines the sizes of both the (outer) sum and all the (inner)
||| products, as well as the types of all the elements of the inner products.
|||
||| A SOP I reflects the structure of a normal Idris datatype. The sum structure
||| represents the choice between the different constructors, the product structure
||| represents the arguments of each constructor.
public export
data SOP' : (k : Type) -> (f : k -> Type) -> (kss : List $ List k) -> Type where
  MkSOP : NS' (List k) (NP' k f) kss -> SOP' k f kss

||| Type alias for `SOP'` with type parameter `k` being
||| implicit. This reflects the kind-polymorphic data type
||| in Haskell.
public export
SOP : {k : Type} -> (f : k -> Type) -> (kss : List (List k)) -> Type
SOP = SOP' k

public export %inline
unSOP : SOP' k f kss -> NS' (List k) (NP' k f) kss
unSOP (MkSOP ns) = ns

--------------------------------------------------------------------------------
--          Specialized Interface Functions
--------------------------------------------------------------------------------

||| Specialiced version of `hmap`
public export
mapSOP : (fun : forall a . f a -> g a) -> SOP f kss -> SOP g kss
mapSOP fun = MkSOP . mapNS (\p => mapNP fun p) . unSOP

||| Specialization of `hap`
public export
hapSOP : POP (\a => f a -> g a) kss -> SOP f kss -> SOP g kss
hapSOP (MkPOP fs) = MkSOP . hliftA2 (\p => hapNP p) fs . unSOP

||| Specialization of `hfoldl`
public export
foldlSOP : (fun : acc -> elem -> acc) -> acc -> SOP (K elem) kss -> acc
foldlSOP fun acc (MkSOP $ Z vs) = foldlNP fun acc vs
foldlSOP fun acc (MkSOP $ S x)  = foldlSOP fun acc (MkSOP x)

||| Specialization of `hfoldr`
public export %inline
foldrSOP : (fun : elem -> acc -> acc) -> acc -> SOP (K elem) kss -> acc
foldrSOP fun acc (MkSOP $ Z vs) = foldrNP fun acc vs
foldrSOP fun acc (MkSOP $ S x)  = foldrSOP fun acc (MkSOP x)

||| Specialization of `hsequence`
public export
sequenceSOP : Applicative g => SOP (\a => g (f a)) kss -> g (SOP f kss)
sequenceSOP = map MkSOP . sequenceNS . mapNS (\p => sequenceNP p) . unSOP

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export %inline
HFunctor k (List $ List k) (SOP' k) where hmap = mapSOP

public export %inline
HAp k (List $ List k) (POP' k) (SOP' k) where hap = hapSOP

public export %inline
HFold k (List $ List k) (SOP' k) where
  hfoldl = foldlSOP
  hfoldr = foldrSOP

public export
HSequence k (List $ List k) (SOP' k) where hsequence = sequenceSOP

public export
POP (Eq . f) kss => Eq (SOP' k f kss) where
  MkSOP a == MkSOP b = a == b

public export
POP (Ord . f) kss => Ord (SOP' k f kss) where
  compare (MkSOP a) (MkSOP b) = compare a b

||| Sums of products have instances of `Semigroup` and `Monoid`
||| only when they consist of a single choice, which must itself be
||| a `Semigroup` or `Monoid`.
public export
POP (Semigroup . f) kss =>
SingletonList kss       => Semigroup (SOP' k f kss) where
  MkSOP a <+> MkSOP b = MkSOP $ a <+> b

||| Sums of products have instances of `Semigroup` and `Monoid`
||| only when they consist of a single choice, which must itself be
||| a `Semigroup` or `Monoid`.
public export
POP (Monoid . f) kss =>
SingletonList kss    => Monoid (SOP' k f kss) where
  neutral = MkSOP neutral

private
mkSOPInjective : MkSOP a = MkSOP b -> a = b
mkSOPInjective Refl = Refl

public export
POP (DecEq . f) kss => DecEq (SOP' k f kss) where
  decEq (MkSOP a) (MkSOP b) with (decEq a b)
    decEq (MkSOP a) (MkSOP a) | Yes Refl   = Yes $ cong MkSOP Refl
    decEq (MkSOP a) (MkSOP b) | No  contra = No (contra . mkSOPInjective)
