module Data.SOP.NP

import Data.SOP.Utils
import Data.SOP.Interfaces

import Decidable.Equality

%default total

||| An n-ary product.
|||
||| The product is parameterized by a type constructor f and indexed by a
||| type-level list ks. The length of the list determines the number of
||| elements in the product, and if the i-th element of the list is of type k,
||| then the i-th element of the product is of type f k.
||| 
||| Two common instantiations of f are the identity functor I and the constant
||| functor K. For I, the product becomes a heterogeneous list, where the
||| type-level list describes the types of its components.  For K a, the product
||| becomes a homogeneous list, where the contents of the type-level list are
||| ignored, but its length still specifies the number of elements.
||| 
||| In the context of the SOP approach to generic programming, an n-ary product
||| describes the structure of the arguments of a single data constructor.
|||
||| Note: `NP'` takes an additional type parameter `k` to simulate
|||       Haskell's kind polymorphism. In theory, this could be left
|||       as an implicit argument. However, type-inference when calling
|||       interface functions like `hpure` was rather poor.
|||
|||       We therefore made `k` explicit and added a type alias `NP`
|||       to be used in most occasions when `k` can be inferred.
|||
||| Examples:
|||
||| ```idris example
||| ex1 : NP I [Char,Bool]
||| ex1 = ['c',False]
|||
||| ex2 : NP (K String) [Char,Bool,Int]
||| ex2 = ["Hello","World","!"]
|||
||| ex3 : NP Maybe [Char,Bool,Int]
||| ex3 = [Just 'x', Nothing, Just 1]
||| ```
public export
data NP' : (k : Type) -> (f : k -> Type) -> (ks : List k) -> Type where
  Nil  : NP' k f []
  (::) : (v : f t) -> (vs : NP' k f ks) -> NP' k f (t :: ks)

||| Type alias for `NP'` with type parameter `k` being
||| implicit. This reflects the kind-polymorphic data type
||| in Haskell.
public export
NP : {k : Type} -> (f : k -> Type) -> (ks : List k) -> Type
NP = NP' k

public export
mapNP : (fun : forall a . f a -> g a) -> NP f ks -> NP g ks
mapNP fun []        = []
mapNP fun (v :: vs) = fun v :: mapNP fun vs

public export
hd : NP f (k :: ks) -> f k
hd (v :: _) = v

public export
tl : NP f (k :: ks) -> NP f ks
tl (_ :: vs) = vs

public export
Projection : (f : k -> Type) -> (ks : List k) -> (v : k) -> Type
Projection f ks v = NP f ks -> f v

public export
shiftProjection : forall v . Projection f ks v -> Projection f (k :: ks) v
shiftProjection g (_ :: vs) = g vs

public export
projections : {ks : _} -> NP (Projection f ks) ks
projections {ks = []}       = []
projections {ks = (_ :: _)} = let ps  = projections {f = f}
                                  fun = shiftProjection {f = f}
                               in hd :: mapNP fun ps

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
Eq (NP' k f []) where
  [] == [] = True

public export
Ord (NP' k f []) where
  compare [] [] = EQ

public export
Semigroup (NP' k f []) where
  [] <+> [] = []

public export
Monoid (NP' k f []) where
  neutral = []

public export
Eq (f t) => Eq (NP' k f ks) => Eq (NP' k f (t :: ks)) where
  (v :: vs) == (w :: ws) = v == w && vs == ws

public export
Ord (f t) => Ord (NP' k f ks) => Ord (NP' k f (t :: ks)) where
  compare (v :: vs) (w :: ws) = compare v w <+> compare vs ws

public export
Semigroup (f t) => Semigroup (NP' k f ks) => Semigroup (NP' k f (t::ks)) where
  (v :: vs) <+> (w :: ws) = (v <+> w) :: (vs <+> ws)

public export
Monoid (f t) => Monoid (NP' k f ks) => Monoid (NP' k f (t::ks)) where
  neutral = neutral :: neutral

public export
HFunctor k (List k) (NP' k) where
   hmap _   []        = []
   hmap fun (v :: vs) = fun v :: hmap fun vs
 
   hcmap c _   []        = []
   hcmap c fun (v :: vs) = fun v :: hcmap c fun vs
 
public export
HPure k (List k) (NP' k) where
  hpure {ks = []}       _ = []
  hpure {ks = (_ :: _)} f = f :: hpure f

  cpure {ks = []}       _ _ = []
  cpure {ks = (_ :: _)} c f = f :: cpure c f

public export
HAp k (List k) (NP' k) where
  hap []        []        = []
  hap (f :: fs) (v :: vs) = f v :: hap fs vs

public export
HFold k (List k) (NP' k) where
  hfoldl _   acc []        = acc
  hfoldl fun acc (v :: vs) = hfoldl fun (fun acc v) vs

  hfoldr _   acc []        = acc
  hfoldr fun acc (v :: vs) = fun v (hfoldr fun acc vs)

public export
HSequence k (List k) (NP' k) where
  hsequence []        = pure []
  hsequence (v :: vs) = [| v :: hsequence vs |]

private
consInjective : Data.SOP.NP.(::) a b = Data.SOP.NP.(::) c d -> (a = c, b = d)
consInjective Refl = (Refl, Refl)

public export
DecEq (NP' k f []) where
  decEq a b = ?res

public export
DecEq (f t) => DecEq (NP' k f ks) => DecEq (NP' k f (t :: ks)) where
  decEq (x :: xs) (y :: ys) with (decEq x y)
    decEq (x :: xs) (y :: ys) | (No contra) =
      No $ contra . fst . consInjective
    decEq (x :: xs) (x :: ys) | (Yes Refl) with (decEq xs ys)
      decEq (x :: xs) (x :: xs) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (x :: xs) (x :: ys) | (Yes Refl) | (No contra) =
        No $ contra . snd . consInjective

--------------------------------------------------------------------------------
--          Examples and Tests
--------------------------------------------------------------------------------

Ex1 : NP I [Char,Bool]
Ex1 = ['c',True]

Ex2 : NP Maybe [Int,Int,Int]
Ex2 = [Nothing,Nothing,Just 2]

Ex3 : NP (K String) [Char,Bool,Int]
Ex3 = ["Hello","World","!"]

EqTest1 : Ex1 == Ex1 = True
EqTest1 = Refl

EqTest2 : Ex1 == ['x',False] = False
EqTest2 = Refl

OrdTest1 : compare Ex1 Ex1 = EQ
OrdTest1 = Refl

OrdTest2 : compare Ex1 ['x',False] = LT
OrdTest2 = Refl

HdTest : hd Ex1 = 'c'
HdTest = Refl

TlTest : tl Ex1 = [True]
TlTest = Refl

SemiTest : the (NP I [String]) ["hello"] <+> ["world"] = ["helloworld"]
SemiTest = Refl

NeutralTest : the (NP I [String,List Int]) Prelude.neutral = ["",[]]
NeutralTest = Refl

HMapTest : hmap Just Ex1 = [Just 'c', Just True]
HMapTest = Refl

HCMapRes : NP (K String) [Char,Bool]
HCMapRes = hcmap Show show Ex1

-- HPureTest : NP Maybe [String,Int]
-- HPureTest = hpure Nothing
-- 
-- CPureNeutralTest : NP I [String,String]
-- CPureNeutralTest = cpure Monoid neutral
