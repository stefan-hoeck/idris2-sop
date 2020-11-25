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
data POP' : (0 k : Type) -> (0 f : k -> Type) -> (0 kss : List (List k)) -> Type where
  Nil  : POP' k f []
  (::) : (vs : NP' k f ks) -> (vss : POP' k f kss) -> POP' k f (ks :: kss)

||| Type alias for `POP'` with type parameter `k` being
||| implicit. This reflects the kind-polymorphic data type
||| in Haskell.
public export
POP : {0 k : Type} -> (0 f : k -> Type) -> (0 kss : List (List k)) -> Type
POP = POP' k

--------------------------------------------------------------------------------
--          Specialized Interface Functions
--------------------------------------------------------------------------------

||| Specialiced version of `hmap`
public export
mapPOP : (fun : forall a . f a -> g a) -> POP f kss -> POP g kss
mapPOP fun []          = []
mapPOP fun (vs :: vss) = mapNP fun vs :: mapPOP fun vss

||| Specialization of `hpure`.
public export
purePOP : {kss : _} -> (forall a . f a) -> POP f kss
purePOP {kss = []}     _ = []
purePOP {kss = _ :: _} f = pureNP f :: purePOP f

||| Specialization of `hap`.
public export
hapPOP : POP (\a => f a -> g a) kss -> POP f kss -> POP g kss
hapPOP []          []          = []
hapPOP (fs :: fss) (vs :: vss) = hapNP fs vs :: hapPOP fss vss

||| Specialization of `hfoldl`
public export
foldlPOP : (fun : acc -> elem -> acc) -> acc -> POP (K elem) kss -> acc
foldlPOP _   acc []          = acc
foldlPOP fun acc (vs :: vss) = foldlPOP fun (foldlNP fun acc vs) vss

||| Specialization of `hfoldr`
public export
foldrPOP : (fun : elem -> acc -> acc) -> acc -> POP (K elem) kss -> acc
foldrPOP _   acc []          = acc
foldrPOP fun acc (vs :: vss) = foldrNP fun (foldrPOP fun acc vss) vs

||| Specialization of `hsequence`
public export
sequencePOP : Applicative g => POP (\a => g (f a)) kss -> g (POP f kss)
sequencePOP []          = pure []
sequencePOP (vs :: vss) = [| sequenceNP vs :: sequencePOP vss |]

--------------------------------------------------------------------------------
--          Interface Conversions
--------------------------------------------------------------------------------

||| This is needed to implement `Ord` below.
public export %hint
ordToEqPOP :  POP (Ord . f) kss -> POP (Eq . f) kss
ordToEqPOP = mapPOP (\_ => materialize Eq)

||| This is needed to implement `Monoid` below.
public export %hint
monoidToSemigroupPOP : POP (Monoid . f) kss -> POP (Semigroup . f) kss
monoidToSemigroupPOP = mapPOP (\_ => materialize Semigroup)

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export %inline
HPure k (List $ List k) (POP' k) where hpure  = purePOP

public export %inline
HFunctor k (List $ List k) (POP' k) where hmap  = mapPOP

public export %inline
HAp k (List $ List k) (POP' k) (POP' k) where hap = hapPOP

public export %inline
HFold k (List $ List k) (POP' k) where
  hfoldl = foldlPOP
  hfoldr = foldrPOP

public export %inline
HSequence k (List $ List k) (POP' k) where hsequence = sequencePOP

public export
(all : POP (Eq . f) kss) => Eq (POP' k f kss) where
  (==) {all = []}     [] []                   = True
  (==) {all = _ :: _} (vs :: vss) (ws :: wss) = vs == ws && vss == wss

public export
(all : POP (Ord . f) kss) => Ord (POP' k f kss) where
  compare {all = []}     [] []                   = EQ
  compare {all = _ :: _} (vs :: vss) (ws :: wss) = compare vs ws <+>
                                                   compare vss wss

public export
(all : POP (Semigroup . f) kss) => Semigroup (POP' k f kss) where
  (<+>) {all = []}     [] []                   = []
  (<+>) {all = _ :: _} (vs :: vss) (ws :: wss) = (vs <+> ws) :: (vss <+> wss)

public export
(all : POP (Monoid . f) kss) => Monoid (POP' k f kss) where
  neutral {all = []}     = []
  neutral {all = _ :: _} = neutral :: neutral

private
consInjective : Data.SOP.POP.(::) a b = Data.SOP.POP.(::) c d -> (a = c, b = d)
consInjective Refl = (Refl, Refl)

public export
(all : POP (DecEq . f) kss) => DecEq (POP' k f kss) where
  decEq {all = []}     []        []        = Yes Refl
  decEq {all = _::_} (vs::vss) (ws::wss) with (decEq vs ws)
    decEq {all = _::_} (vs::vss) (ws::wss) | (No contra) =
      No $ contra . fst . consInjective
    decEq {all = _::_} (vs::vss) (vs::wss) | (Yes Refl) with (decEq vss wss)
      decEq {all = _::_} (vs::vss) (vs::vss) | (Yes Refl) | (Yes Refl) =
        Yes Refl
      decEq {all = _::_} (vs::vss) (vs::wss) | (Yes Refl) | (No contra) =
        No $ contra . snd . consInjective
