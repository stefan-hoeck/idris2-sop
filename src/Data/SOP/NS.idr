module Data.SOP.NS

import Data.SOP.Utils
import Data.SOP.Interfaces

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
data NS' : (0 k : Type) -> (f : k -> Type) -> (ks : List k) -> Type where
  Z : (v : f t)  -> NS' k f (t :: ks)
  S : NS' k f ks -> NS' k f (t :: ks)

||| Type alias for `NS'` with type parameter `k` being
||| implicit. This reflects the kind-polymorphic data type
||| in Haskell.
public export
NS : {0 k : Type} -> (f : k -> Type) -> (ks : List k) -> Type
NS = NS' k

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
Eq (NS' k f []) where
  a == b impossible

public export
Ord (NS' k f []) where
  compare a b impossible

public export
Eq (f t) => Eq (NS' k f ks) => Eq (NS' k f (t :: ks)) where
  (Z v)  == (Z w)  = v == w
  (S vs) == (S ws) = vs == ws
  _      == _      = False

public export
Ord (f t) => Ord (NS' k f ks) => Ord (NS' k f (t :: ks)) where
  compare (Z v)  (Z w)  = compare v w
  compare (Z _)  (S _)  = LT
  compare (S _)  (Z _)  = GT
  compare (S vs) (S ws) = compare vs ws

public export
HFunctor k (List k) (NS' k) where
  hmap fun (Z v) = Z $ fun v
  hmap fun (S x) = S $ hmap fun x

  hcmap c fun (Z v) = Z $ fun v
  hcmap c fun (S x) = S $ hcmap c fun x
 
public export
HFold k (List k) (NS' k) where
  hfoldl fun acc (Z v) = fun acc v
  hfoldl fun acc (S x) = hfoldl fun acc x
  
  hfoldr fun acc (Z v) = fun v acc
  hfoldr fun acc (S x) = hfoldr fun acc x

public export
HSequence k (List k) (NS' k) where
  hsequence (Z v) = map Z v
  hsequence (S x) = map S $ hsequence x

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
DecEq (NS' k f []) where
  decEq a b impossible

public export
DecEq (f t) => DecEq (NS' k f ks) => DecEq (NS' k f (t :: ks)) where
  decEq (Z x) (Z y) with (decEq x y)
    decEq (Z x) (Z x) | Yes Refl = Yes Refl
    decEq (Z x) (Z y) | No contra = No (contra . zInjective)
  decEq (Z x) (S y) = No absurd
  decEq (S x) (Z y) = No absurd
  decEq (S x) (S y) with (decEq x y)
    decEq (S x) (S x) | Yes Refl = Yes Refl
    decEq (S x) (S y) | No contra = No (contra . sInjective)

--------------------------------------------------------------------------------
--          Examples and Tests
--------------------------------------------------------------------------------

Ex1 : let T = NS I [Char,Bool] in (T,T)
Ex1 = (Z 'x', S $ Z False)
