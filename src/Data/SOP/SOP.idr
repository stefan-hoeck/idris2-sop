module Data.SOP.SOP

import Data.SOP.NP
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
data SOP' : (0 k : Type) -> (0 f : k -> Type) -> (0 kss : List $ List k) -> Type where
  Z : (vs : NP' k f ks)  -> SOP' k f (ks :: kss)
  S : SOP' k f kss -> SOP' k f (ks :: kss)

||| Type alias for `SOP'` with type parameter `k` being
||| implicit. This reflects the kind-polymorphic data type
||| in Haskell.
public export
SOP : {0 k : Type} -> (0 f : k -> Type) -> (0 kss : List (List k)) -> Type
SOP = SOP' k

--------------------------------------------------------------------------------
--          Specialized Interface Functions
--------------------------------------------------------------------------------

||| Specialiced version of `hmap`
public export
mapSOP : (fun : forall a . f a -> g a) -> SOP f kss -> SOP g kss
mapSOP fun (Z vs) = Z $ mapNP fun vs
mapSOP fun (S x)  = S $ mapSOP fun x

||| Specialization of `hfoldl`
public export
foldlSOP : (fun : acc -> elem -> acc) -> acc -> SOP (K elem) kss -> acc
foldlSOP fun acc (Z vs) = foldlNP fun acc vs
foldlSOP fun acc (S x)  = foldlSOP fun acc x

||| Specialization of `hfoldr`
public export %inline
foldrSOP : (fun : elem -> acc -> acc) -> acc -> SOP (K elem) kss -> acc
foldrSOP fun acc (Z vs) = foldrNP fun acc vs
foldrSOP fun acc (S x)  = foldrSOP fun acc x

||| Specialization of `hsequence`
public export
sequenceSOP : Applicative g => SOP (\a => g (f a)) kss -> g (SOP f kss)
sequenceSOP (Z vs) = Z <$> sequenceNP vs
sequenceSOP (S x)  = S <$> sequenceSOP x

||| Specialization of `hap`
public export
hapSOP : POP (\a => f a -> g a) kss -> SOP f kss -> SOP g kss
hapSOP (funs :: _)     (Z vs) = Z $ hapNP funs vs
hapSOP (_    :: funss) (S y)  = S $ hapSOP funss y

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
(all : POP (Eq . f) kss) => Eq (SOP' k f kss) where
  (==) {all = _::_} (Z vs) (Z ws) = vs == ws
  (==) {all = _::_} (S x)  (S y)  = x  == y
  (==) {all = _::_} _      _      = False

public export
(all : POP (Ord . f) kss) => Ord (SOP' k f kss) where
  compare {all = _::_} (Z vs) (Z ws) = compare vs ws
  compare {all = _::_} (S x)  (S y)  = compare x y
  compare {all = _::_} (Z _)  (S _)  = LT
  compare {all = _::_} (S _)  (Z _)  = GT

||| Sums of products have instances of `Semigroup` and `Monoid`
||| only when they consist of a single choice, which must itself be
||| a `Semigroup` or `Monoid`.
public export
(all : POP (Semigroup . f) kss) =>
(prf : SingletonList kss) => Semigroup (SOP' k f kss) where
  (<+>) {all = _ :: _} {prf = IsSingletonList _} (Z l) (Z r) = Z $ l <+> r
  (<+>) {all = _ :: _} {prf = IsSingletonList _} (S _) _    impossible
  (<+>) {all = _ :: _} {prf = IsSingletonList _} _    (S _) impossible

||| Sums of products have instances of `Semigroup` and `Monoid`
||| only when they consist of a single choice, which must itself be
||| a `Semigroup` or `Monoid`.
public export
(all : POP (Monoid . f) kss) =>
(prf : SingletonList kss) => Monoid (SOP' k f kss) where
  neutral {all = _ :: _} {prf = IsSingletonList _} = Z neutral

public export
Uninhabited (Data.SOP.SOP.Z x = Data.SOP.SOP.S y) where
  uninhabited Refl impossible

public export
Uninhabited (Data.SOP.SOP.S x = Data.SOP.SOP.Z y) where
  uninhabited Refl impossible

private
zInjective : Data.SOP.SOP.Z x = Data.SOP.SOP.Z y -> x = y
zInjective Refl = Refl

private
sInjective : Data.SOP.SOP.S x = Data.SOP.SOP.S y -> x = y
sInjective Refl = Refl

public export
(all : POP (DecEq . f) kss) => DecEq (SOP' k f kss) where
  decEq {all = _::_} (Z xs) (Z ys) with (decEq xs ys)
    decEq {all = _::_} (Z xs) (Z xs) | Yes Refl = Yes Refl
    decEq {all = _::_} (Z xs) (Z ys) | No contra = No (contra . zInjective)
  decEq {all = _::_} (Z xs) (S y) = No absurd
  decEq {all = _::_} (S x) (Z ys) = No absurd
  decEq {all = _::_} (S x) (S y) with (decEq x y)
    decEq {all = _::_} (S x) (S x) | Yes Refl = Yes Refl
    decEq {all = _::_} (S x) (S y) | No contra = No (contra . sInjective)
