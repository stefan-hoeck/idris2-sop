module Data.SOP.NP

import Data.SOP.Utils
import Data.SOP.Interfaces

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
data NP : forall k . (f : k -> Type) -> (ks : List k) -> Type where
  Nil  : NP f []
  (::) : {0 t : k} -> (v : f t) -> (vs : NP f ks) -> NP f (t :: ks)

public export
mapNP : (fun : forall k . f k -> g k) -> NP f ks -> NP g ks
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
All (Eq . f) ks => Eq (NP f ks) where
  []        == []        = True
  (v :: vs) == (w :: ws) = v == w && vs == ws

public export
All (Eq . f) ks => All (Ord . f) ks => Ord (NP f ks) where
  compare [] []               = EQ
  compare (v :: vs) (w :: ws) = compare v w <+> compare vs ws

public export
All (Semigroup . f) ks => Semigroup (NP f ks) where
  []        <+> []        = []
  (v :: vs) <+> (w :: ws) = (v <+> w) :: (vs <+> ws)

public export
{ks : _} -> All (Semigroup . f) ks => All (Monoid . f) ks => Monoid (NP f ks) where
  neutral {ks = []}     = []
  neutral {ks = _ :: _} = neutral :: neutral

public export
HPure NP where
  hpure {ks = []}       _ = []
  hpure {ks = (_ :: _)} f = f :: hpure {h = NP} f

  cpure {ks = []}       _ _ = []
  cpure {ks = (_ :: _)} c f = f :: cpure {h = NP} c f

public export
HAp NP where
  hap fun []        = []
  hap fun (v :: vs) = fun v :: hap {h = NP} fun vs

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

NothingTest : NP Maybe [String,Int]
NothingTest = hpure {h = NP} Nothing

EmptyTest : NP I [String,String]
EmptyTest = cpure {h = NP} Monoid neutral
