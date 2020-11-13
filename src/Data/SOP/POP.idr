module Data.SOP.POP

import Data.SOP.Utils
import Data.SOP.Interfaces
import Data.SOP.NP

%default total

public export
data POP' : (k : Type) -> (f : k -> Type) -> (kss : List (List k)) -> Type where
  Nil  : POP' k f []
  (::) : (vs : NP' k f ks) -> (vss : POP' k f kss) -> POP' k f (ks :: kss)

||| Type alias for `POP'` with type parameter `k` being
||| implicit. This reflects the kind-polymorphic data type
||| in Haskell.
public export
POP : {k : Type} -> (f : k -> Type) -> (kss : List (List k)) -> Type
POP = POP' k

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
HFunctor k (List $ List (k)) (POP' k) where
   hmap _   []          = []
   hmap fun (vs :: vss) = hmap fun vs :: hmap fun vss
 
   hcmap c _   []          = []
   hcmap c fun (vs :: vss) = hcmap c fun vs :: hcmap c fun vss
 
public export
HPure k (List $ List k) (POP' k) where
  hpure {ks = []}       _ = []
  hpure {ks = (_ :: _)} f = hpure f :: hpure f

  cpure {ks = []}       _ _ = []
  cpure {ks = (_ :: _)} c f = cpure c f :: cpure c f

public export
HAp k (List $ List k) (POP' k) where
  hap []          []          = []
  hap (fs :: fss) (vs :: vss) = hap fs vs :: hap fss vss

public export
HFold k (List $ List k) (POP' k) where
  hfoldl _   acc []          = acc
  hfoldl fun acc (vs :: vss) = hfoldl fun (hfoldl fun acc vs) vss

  hfoldr _   acc []          = acc
  hfoldr fun acc (vs :: vss) = hfoldr fun (hfoldr fun acc vs) vs

public export
HSequence k (List $ List k) (POP' k) where
  hsequence []          = pure []
  hsequence (vs :: vss) = [| hsequence vs :: hsequence vss |]
