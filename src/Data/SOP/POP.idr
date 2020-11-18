module Data.SOP.POP

import Data.SOP.Utils
import Data.SOP.Interfaces
import Data.SOP.NP

import Decidable.Equality

%default total

||| A product of products.
||| 
||| Unlike in the Haskell version, not using a Newtype here allows us
||| to overload the constructor names of `NP'`.
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
data POP' : (0 k : Type) -> (f : k -> Type) -> (kss : List (List k)) -> Type where
  Nil  : POP' k f []
  (::) : (vs : NP' k f ks) -> (vss : POP' k f kss) -> POP' k f (ks :: kss)

||| Type alias for `POP'` with type parameter `k` being
||| implicit. This reflects the kind-polymorphic data type
||| in Haskell.
public export
POP : {0 k : Type} -> (f : k -> Type) -> (kss : List (List k)) -> Type
POP = POP' k

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
Eq (POP' k f []) where
  [] == [] = True

public export
Ord (POP' k f []) where
  compare [] [] = EQ

public export
Semigroup (POP' k f []) where
  [] <+> [] = []

public export
Monoid (POP' k f []) where
  neutral = []

public export
Eq (NP' k f ks) => Eq (POP' k f kss) => Eq (POP' k f (ks :: kss)) where
  (vs :: vss) == (ws :: wss) = vs == ws && vss == wss

public export
Ord (NP' k f ks) => Ord (POP' k f kss) => Ord (POP' k f (ks :: kss)) where
  compare (vs :: vss) (ws :: wss) = compare vs ws <+> compare vss wss

public export
Semigroup (NP' k f ks) =>
Semigroup (POP' k f kss) => Semigroup (POP' k f (ks::kss)) where
  (vs :: vss) <+> (ws :: wss) = (vs <+> ws) :: (vss <+> wss)

public export
Monoid (NP' k f ks) =>
Monoid (POP' k f kss) => Monoid (POP' k f (ks::kss)) where
  neutral = neutral :: neutral

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

  hcpure {ks = []}       _ _ = []
  hcpure {ks = (_ :: _)} c f = hcpure c f :: hcpure c f

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

private
consInjective : Data.SOP.POP.(::) a b = Data.SOP.POP.(::) c d -> (a = c, b = d)
consInjective Refl = (Refl, Refl)

public export
DecEq (POP' k f []) where
  decEq [] [] = Yes Refl

public export
DecEq (NP' k f ks) =>
DecEq (POP' k f kss) => DecEq (POP' k f (ks :: kss)) where
  decEq (x :: xs) (y :: ys) with (decEq x y)
    decEq (x :: xs) (y :: ys) | (No contra) =
      No $ contra . fst . consInjective
    decEq (x :: xs) (x :: ys) | (Yes Refl) with (decEq xs ys)
      decEq (x :: xs) (x :: xs) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (x :: xs) (x :: ys) | (Yes Refl) | (No contra) =
        No $ contra . snd . consInjective
