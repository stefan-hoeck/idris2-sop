module Data.SOP.SOP

import Data.SOP.NP
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
--          Implementations
--------------------------------------------------------------------------------

public export
Eq (SOP' k f []) where
  a == b impossible

public export
Ord (SOP' k f []) where
  compare a b impossible

public export
Eq (NP' k f ks) => Eq (SOP' k f kss) => Eq (SOP' k f (ks :: kss)) where
  (Z vs)  == (Z ws)  = vs == ws
  (S vss) == (S wss) = vss == wss
  _       == _       = False

public export
Ord (NP' k f ks) => Ord (SOP' k f kss) => Ord (SOP' k f (ks :: kss)) where
  compare (Z vs) (Z ws)   = compare vs ws
  compare (Z _)  (S _)    = LT
  compare (S _)  (Z _)    = GT
  compare (S vss) (S wss) = compare vss wss


public export
HFunctor k (List $ List k) (SOP' k) where
  hmap fun (Z v) = Z $ hmap fun v
  hmap fun (S x) = S $ hmap fun x

  hcmap c fun (Z v) = Z $ hcmap c fun v
  hcmap c fun (S x) = S $ hcmap c fun x

public export
HFold k (List $ List k) (SOP' k) where
  hfoldl fun acc (Z v) = hfoldl fun acc v
  hfoldl fun acc (S x) = hfoldl fun acc x
  
  hfoldr fun acc (Z v) = hfoldr fun acc v
  hfoldr fun acc (S x) = hfoldr fun acc x

public export
HSequence k (List $ List k) (SOP' k) where
  hsequence (Z v) = map Z $ hsequence v
  hsequence (S x) = map S $ hsequence x

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
DecEq (SOP' k f []) where
  decEq a b impossible

public export
DecEq (NP' k f ks) => DecEq (SOP' k f kss) => DecEq (SOP' k f (ks :: kss)) where
  decEq (Z x) (Z y) with (decEq x y)
    decEq (Z x) (Z x) | Yes Refl = Yes Refl
    decEq (Z x) (Z y) | No contra = No (contra . zInjective)
  decEq (Z x) (S y) = No absurd
  decEq (S x) (Z y) = No absurd
  decEq (S x) (S y) with (decEq x y)
    decEq (S x) (S x) | Yes Refl = Yes Refl
    decEq (S x) (S y) | No contra = No (contra . sInjective)
