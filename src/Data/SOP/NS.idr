module Data.SOP.NS

import Data.List.Elem
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
||| the (NS_ Type I [Char,Bool]) (Z 'x')
||| the (NS_ Type I [Char,Bool]) (S $ Z False)
||| ```
public export
data NS_ : (k : Type) -> (f : k -> Type) -> (ks : List k) -> Type where
  Z : (v : f t)  -> NS_ k f (t :: ks)
  S : NS_ k f ks -> NS_ k f (t :: ks)

||| Type alias for `NS_` with type parameter `k` being
||| implicit. This reflects the kind-polymorphic data type
||| in Haskell.
public export
NS : {k : Type} -> (f : k -> Type) -> (ks : List k) -> Type
NS = NS_ k

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
foldrNS : (fun : elem -> Lazy acc -> acc) -> Lazy acc -> NS (K elem) ks -> acc
foldrNS fun acc (Z v) = fun v acc
foldrNS fun acc (S x) = foldrNS fun acc x

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

||| Specialization of `hcollapse`
public export
collapseNS : NS (K a) ks -> a
collapseNS (Z v) = v
collapseNS (S x) = collapseNS x

--------------------------------------------------------------------------------
--          Injections
--------------------------------------------------------------------------------

||| An injection into an n-ary sum takes a value of the correct
||| type and wraps it in one of the sum's possible choices.
public export
0 Injection : (f : k -> Type) -> (ks : List k) -> (v : k) -> Type
Injection f ks v = f v -> K (NS f ks) v

||| The set of injections into an n-ary sum `NS f ks` can
||| be wrapped in a corresponding n-ary product.
public export
injectionsNP : NP g ks -> NP (Injection f ks) ks
injectionsNP []       = []
injectionsNP (_ :: t) = Z :: mapNP (S .) (injectionsNP t)

||| The set of injections into an n-ary sum `NS f ks` can
||| be wrapped in a corresponding n-ary product.
public export
injections : {ks : _} -> NP (Injection f ks) ks
injections = injectionsNP (pureNP ())

||| Applies all injections to an n-ary product of values.
|||
||| This is not implemented in terms of injections for the
||| following reason: Since we have access to the structure
||| of the n-ary product and thus `ks`, we do not need a
||| runtime reference of `ks`. Therefore, when applying
||| injections to an n-ary product, prefer this function
||| over a combination involving `injections`.
public export
apInjsNP_ : NP f ks -> NP (K $ NS f ks) ks
apInjsNP_ []        = []
apInjsNP_ (v :: vs) = Z v :: mapNP S (apInjsNP_ vs)

||| Alias for `collapseNP . apInjsNP_`
public export
apInjsNP : NP f ks -> List (NS f ks)
apInjsNP = collapseNP . apInjsNP_

--------------------------------------------------------------------------------
--          Extracting and injecting values
--------------------------------------------------------------------------------

||| Injects a value into an n-ary sum.
public export
inject : {0 t : k} -> (v : f t) -> {auto prf : Elem t ks} -> NS f ks
inject v {prf = Here}    = Z v
inject v {prf = There _} = S $ inject v

||| Tries to extract a value of the given type from an n-ary sum.
public export
extract : (0 t : k) -> NS f ks -> {auto prf : Elem t ks} -> Maybe (f t)
extract _ (Z v) {prf = Here}    = Just v
extract _ (S _) {prf = Here}    = Nothing
extract _ (Z _) {prf = There y} = Nothing
extract t (S x) {prf = There y} = extract t x

||| Converts an n-ary sum into the corresponding n-ary product
||| of alternatives.
public export
toNP : {ks : _} -> Alternative g => NS f ks -> NP (g . f) ks
toNP {ks = _ :: _} (Z v) = pure v :: hpure empty
toNP {ks = _ :: _} (S x) = empty  :: toNP x

--------------------------------------------------------------------------------
--          Expanding sums
--------------------------------------------------------------------------------

||| Injects an n-ary sum into a larger n-ary sum.
public export
expand : NS f ks -> {auto prf: Sublist ks ks'} -> NS f ks'
expand (Z v) {prf = SLSame y} = Z v
expand (S x) {prf = SLSame y} = S $ expand x
expand v     {prf = SLDiff y} = S $ expand v
expand _     {prf = SLNil} impossible

||| Tries to narrow down an n-ary sum to a subset of
||| choices. `ks'` must be a sublist (values in the same order) of `ks`.
public export
narrow : NS f ks -> {auto prf: Sublist ks' ks} -> Maybe (NS f ks')
narrow _     {prf = SLNil}    = Nothing
narrow (Z v) {prf = SLSame x} = Just $ Z v
narrow (Z v) {prf = SLDiff x} = Nothing
narrow (S x) {prf = SLSame y} = S <$> narrow x
narrow (S x) {prf = SLDiff y} = narrow x

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export %inline
HFunctor k (List k) (NS_ k) where hmap = mapNS

public export %inline
HAp k (List k) (NP_ k) (NS_ k) where hap = hapNS

public export %inline
HFold k (List k) (NS_ k) where
  hfoldl = foldlNS
  hfoldr = foldrNS

public export
HSequence k (List k) (NS_ k) where hsequence = sequenceNS

public export
HCollapse k (List k) (NS_ k) I where hcollapse = collapseNS

public export
(all : NP (Eq . f) ks) => Eq (NS_ k f ks) where
  (==) {all = _::_} (Z v) (Z w) = v == w
  (==) {all = _::_} (S x) (S y) = x == y
  (==) {all = _::_} _     _     = False

public export
(all : NP (Ord . f) ks) => Ord (NS_ k f ks) where
  compare {all = _::_} (Z v) (Z w) = compare v w
  compare {all = _::_} (S x) (S y) = compare x y
  compare {all = _::_} (Z _) (S _) = LT
  compare {all = _::_} (S _) (Z _) = GT

||| Sums have instances of `Semigroup` and `Monoid`
||| only when they consist of a single choice, which must itself be
||| a `Semigroup` or `Monoid`.
public export
(all : NP (Semigroup . f) [k']) =>
Semigroup (NS_ k f [k']) where
  (<+>) {all = _ :: _} (Z l) (Z r) = Z $ l <+> r
  (<+>) {all = _ :: _} (S _) _    impossible
  (<+>) {all = _ :: _} _    (S _) impossible

public export
(all : NP (Show . f) ks) => Show (NS_ k f ks) where
  showPrec {all = _::_} p (Z v) = showCon p "Z" (showArg v)
  showPrec {all = _::_} p (S x) = showCon p "S" (showPrec App x)

||| Sums have instances of `Semigroup` and `Monoid`
||| only when they consist of a single choice, which must itself be
||| a `Semigroup` or `Monoid`.
public export
(all : NP (Monoid . f) [k']) => Monoid (NS_ k f [k']) where
  neutral {all = _ :: _} = Z neutral

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
(all : NP (DecEq . f) ks) => DecEq (NS_ k f ks) where
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
