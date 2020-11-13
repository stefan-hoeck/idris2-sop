module Data.SOP.NS

import Data.SOP.Utils
import Data.SOP.Interfaces

%default total

public export
data NS' : (k : Type) -> (f : k -> Type) -> (ks : List k) -> Type where
  Z : (v : f t)  -> NS' k f (t :: ks)
  S : NS' k f ks -> NS' k f (t :: ks)

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
All (Eq . f) ks => Eq (NS' k f ks) where
  (Z x) == (Z y) = x == y
  (S x) == (S y) = x == y
  _     == _     = False

public export
All (Eq . f) ks => All (Ord . f) ks => Ord (NS' k f ks) where
  compare (Z x) (Z y) = compare x y
  compare (Z _) (S _) = LT
  compare (S _) (Z _) = GT
  compare (S x) (S y) = compare y x

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
