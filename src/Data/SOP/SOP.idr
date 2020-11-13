module Data.SOP.SOP

import Data.SOP.NP
import Data.SOP.Utils
import Data.SOP.Interfaces

import Decidable.Equality

%default total

public export
data SOP' : (k : Type) -> (f : k -> Type) -> (kss : List $ List k) -> Type where
  Z : (vs : NP' k f ks)  -> SOP' k f (ks :: kss)
  S : SOP' k f kss -> SOP' k f (ks :: kss)

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
All (Eq . f) kss => Eq (SOP' k f kss) where
  (Z x) == (Z y) = x == y
  (S x) == (S y) = x == y
  _     == _     = False

public export
All (Eq . f) ks => All (Ord . f) ks => Ord (SOP' k f ks) where
  compare (Z x) (Z y) = compare x y
  compare (Z _) (S _) = LT
  compare (S _) (Z _) = GT
  compare (S x) (S y) = compare y x

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

export
All (DecEq . f) ks => DecEq (SOP' k f ks) where
  decEq (Z x) (Z y) with (decEq x y)
   decEq (Z x) (Z x) | Yes Refl = Yes Refl
   decEq (Z x) (Z y) | No contra = No (contra . zInjective)
  decEq (Z x) (S y) = No absurd
  decEq (S x) (Z y) = No absurd
  decEq (S x) (S y) with (decEq x y)
   decEq (S x) (S x) | Yes Refl = Yes Refl
   decEq (S x) (S y) | No contra = No (contra . sInjective)
