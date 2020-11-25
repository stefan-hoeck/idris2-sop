module Data.SOP.NS

import Data.SOP.Interfaces
import Data.SOP.NP
import Data.SOP.Utils

import Decidable.Equality

%default total

||| An n-ary sum.
|||
||| The sum is parameterized by a type constructor f and indexed by a
||| type-level list xs. The length of the list determines the number of choices
||| in the sum and if the i-th element of the list is of type x, then the i-th
||| choice of the sum is of type f x.
|||
||| The constructor names are chosen to resemble Peano-style natural numbers,
||| i.e., Z is for "zero", and S is for "successor". Chaining S and Z chooses
||| the corresponding component of the sum.
|||
||| Note that empty sums (indexed by an empty list) have no non-bottom
||| elements.
|||
||| Two common instantiations of f are the identity functor I and the constant
||| functor K. For I, the sum becomes a direct generalization of the Either
||| type to arbitrarily many choices. For K a, the result is a homogeneous
||| choice type, where the contents of the type-level list are ignored, but its
||| length specifies the number of options.
|||
||| In the context of the SOP approach to generic programming, an n-ary sum
||| describes the top-level structure of a datatype, which is a choice between
||| all of its constructors.
|||
||| Examples:
|||
||| ```idris example
||| the (NS' Type I [Char,Bool]) (Z 'x')
||| the (NS' Type I [Char,Bool]) (S $ Z False)
||| ```
public export
data NS' : (0 k : Type) -> (0 f : k -> Type) -> (0 ks : List k) -> Type where
  Z : (v : f t)  -> NS' k f (t :: ks)
  S : NS' k f ks -> NS' k f (t :: ks)

||| Type alias for `NS'` with type parameter `k` being
||| implicit. This reflects the kind-polymorphic data type
||| in Haskell.
public export
NS : {0 k : Type} -> (0 f : k -> Type) -> (0 ks : List k) -> Type
NS = NS' k

--------------------------------------------------------------------------------
--          Specialized Interface Functions
--------------------------------------------------------------------------------

||| Specialiced version of `hmap`
public export
mapNS : (fun : forall a . f a -> g a) -> NS f ks -> NS g ks
mapNS fun (Z v) = Z $ fun v
mapNS fun (S x) = S $ mapNS fun x

||| Specialization of `hfoldl`
public export
foldlNS : (fun : acc -> elem -> acc) -> acc -> NS (K elem) ks -> acc
foldlNS fun acc (Z v) = fun acc v
foldlNS fun acc (S x) = foldlNS fun acc x

||| Specialization of `hfoldr`
public export %inline
foldrNS : (fun : elem -> acc -> acc) -> acc -> NS (K elem) ks -> acc
foldrNS fun acc = foldlNS (flip fun) acc

||| Specialization of `hsequence`
public export
sequenceNS : Applicative g => NS (\a => g (f a)) ks -> g (NS f ks)
sequenceNS (Z v) = map Z v
sequenceNS (S x) = S <$> sequenceNS x

||| Specialization of `hap`
public export
hapNS : NP (\a => f a -> g a) ks -> NS f ks -> NS g ks
hapNS (fun :: _)    (Z v) = Z $ fun v
hapNS (_   :: funs) (S y) = S $ hapNS funs y

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export %inline
HFunctor k (List k) (NS' k) where hmap = mapNS

public export %inline
HAp k (List k) (NP' k) (NS' k) where hap = hapNS

public export %inline
HFold k (List k) (NS' k) where
  hfoldl = foldlNS
  hfoldr = foldrNS

public export
HSequence k (List k) (NS' k) where hsequence = sequenceNS

public export
(all : NP (Eq . f) ks) => Eq (NS' k f ks) where
  (==) {all = _::_} (Z v) (Z w) = v == w
  (==) {all = _::_} (S x) (S y) = x == y
  (==) {all = _::_} _     _     = False

public export
(all : NP (Ord . f) ks) => Ord (NS' k f ks) where
  compare {all = _::_} (Z v) (Z w) = compare v w
  compare {all = _::_} (S x) (S y) = compare x y
  compare {all = _::_} (Z _) (S _) = LT
  compare {all = _::_} (S _) (Z _) = GT

public export
Uninhabited (Data.SOP.NS.Z x = Data.SOP.NS.S y) where
  uninhabited Refl impossible

public export
Uninhabited (Data.SOP.NS.S x = Data.SOP.NS.Z y) where
  uninhabited Refl impossible

private
zInjective : Data.SOP.NS.Z x = Data.SOP.NS.Z y -> x = y
zInjective Refl = Refl

private
sInjective : Data.SOP.NS.S x = Data.SOP.NS.S y -> x = y
sInjective Refl = Refl

public export
(all : NP (DecEq . f) ks) => DecEq (NS' k f ks) where
  decEq {all = _::_} (Z x) (Z y) with (decEq x y)
    decEq {all = _::_} (Z x) (Z x) | Yes Refl = Yes Refl
    decEq {all = _::_} (Z x) (Z y) | No contra = No (contra . zInjective)
  decEq {all = _::_} (Z x) (S y) = No absurd
  decEq {all = _::_} (S x) (Z y) = No absurd
  decEq {all = _::_} (S x) (S y) with (decEq x y)
    decEq {all = _::_} (S x) (S x) | Yes Refl = Yes Refl
    decEq {all = _::_} (S x) (S y) | No contra = No (contra . sInjective)

--------------------------------------------------------------------------------
--          Examples and Tests
--------------------------------------------------------------------------------

Ex1 : let T = NS I [Char,Bool] in (T,T)
Ex1 = (Z 'x', S $ Z False)
