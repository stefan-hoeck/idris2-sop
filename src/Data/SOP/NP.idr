module Data.SOP.NP

import Data.List.Elem
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
|||       interface functions like `hpure` was rather poor with `k`
|||       being implicit.
|||
|||       We therefore made `k` explicit and added a type alias `NP`
|||       to be used in those occasions when `k` can be inferred.
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

--------------------------------------------------------------------------------
--          Specialized Interface Functions
--------------------------------------------------------------------------------

||| Specialiced version of `hmap`
public export
mapNP : (fun : forall a . f a -> g a) -> NP f ks -> NP g ks
mapNP fun []        = []
mapNP fun (v :: vs) = fun v :: mapNP fun vs

||| Specialization of `hpure`.
public export
pureNP : {ks : _} -> (forall a . f a) -> NP f ks
pureNP {ks = []}     _ = []
pureNP {ks = _ :: _} f = f :: pureNP f

||| Specialization of `hap`.
public export
hapNP : NP (\a => f a -> g a) ks -> NP f ks -> NP g ks
hapNP []        []        = []
hapNP (f :: fs) (v :: vs) = f v :: hapNP fs vs

||| Specialization of `hfoldl`
public export
foldlNP : (fun : acc -> elem -> acc) -> acc -> NP (K elem) ks -> acc
foldlNP _   acc []        = acc
foldlNP fun acc (v :: vs) = foldlNP fun (fun acc v) vs

||| Specialization of `hfoldr`
public export
foldrNP : (fun : elem -> acc -> acc) -> acc -> NP (K elem) ks -> acc
foldrNP _   acc []        = acc
foldrNP fun acc (v :: vs) = fun v (foldrNP fun acc vs)

||| Specialization of `hsequence`
public export
sequenceNP : Applicative g => NP (\a => g (f a)) ks -> g (NP f ks)
sequenceNP []        = pure []
sequenceNP (v :: vs) = [| v :: sequenceNP vs |]

--------------------------------------------------------------------------------
--          Core Functions
--------------------------------------------------------------------------------

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
--          Accessing Values
--------------------------------------------------------------------------------

||| Access the first element of the given type in
||| an n-ary product
public export
get : (t : k) -> {auto prf : Elem t ks} -> NP' k f ks -> f t
get t {prf = Here}    (v :: _) = v
get t {prf = There _} (_ :: vs) = get t vs

--------------------------------------------------------------------------------
--          Modifying Values
--------------------------------------------------------------------------------

public export
data UpdateElem :  (t : k)
                -> (t' : k)
                -> (ks : List k)
                -> (ks' : List k)
                -> Type where
  UpdateHere  : UpdateElem t t' (t :: ks) (t' :: ks)
  UpdateThere : UpdateElem t t' ks ks' -> UpdateElem t t' (k :: ks) (k :: ks')

||| Modify the first element of the given type
||| in an n-ary product, thereby possibly changing the
||| types of stored values.
public export
modify :  (fun : f t -> f t')
       -> {auto prf : UpdateElem t t' ks ks'}
       -> NP' k f ks
       -> NP' k f ks'
modify fun {prf = UpdateHere}    (v :: vs) = fun v :: vs
modify fun {prf = UpdateThere _} (v :: vs) = v :: modify fun vs

||| Replaces the first element of the given type
||| in an n-ary product, thereby possibly changing the
||| types of stored values.
public export
setAt :  (0 t : k)
      -> (v' : f t')
      -> {auto prf : UpdateElem t t' ks ks'}
      -> NP' k f ks
      -> NP' k f ks'
setAt _ v' {prf = UpdateHere}    (_ :: vs) = v' :: vs
setAt t v' {prf = UpdateThere y} (v :: vs) = v :: setAt t v' vs

||| Alias for `setAt` for those occasions when
||| Idris cannot infer the type of the new value.
public export
setAt' :  (0 t  : k)
       -> (0 t' : k)
       -> (v' : f t')
       -> {auto prf : UpdateElem t t' ks ks'}
       -> NP' k f ks
       -> NP' k f ks'
setAt' t _ v' np = setAt t v' np

--------------------------------------------------------------------------------
--          Interface Conversions
--------------------------------------------------------------------------------

||| This is needed to implement `Ord` below.
public export %hint
ordToEqNP : NP (Ord . f) ks -> NP (Eq . f) ks
ordToEqNP = mapNP (\_ => materialize Eq)

||| This is needed to implement `Monoid` below.
public export %hint
monoidToSemigroupNP : NP (Monoid . f) ks -> NP (Semigroup . f) ks
monoidToSemigroupNP = mapNP (\_ => materialize Semigroup)

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export %inline
HPure k (List k) (NP' k) where hpure  = pureNP

public export %inline
HFunctor k (List k) (NP' k) where hmap  = mapNP

public export %inline
HAp k (List k) (NP' k) (NP' k) where hap = hapNP

public export %inline
HFold k (List k) (NP' k) where
  hfoldl = foldlNP
  hfoldr = foldrNP

public export %inline
HSequence k (List k) (NP' k) where hsequence = sequenceNP

public export
(all : NP (Eq . f) ks) => Eq (NP' k f ks) where
  (==) {all = []}     [] []               = True
  (==) {all = _ :: _} (v :: vs) (w :: ws) = v == w && vs == ws

public export
(all : NP (Ord . f) ks) => Ord (NP' k f ks) where
  compare {all = []}     [] []               = EQ
  compare {all = _ :: _} (v :: vs) (w :: ws) = compare v w <+> compare vs ws

public export
(all : NP (Semigroup . f) ks) => Semigroup (NP' k f ks) where
  (<+>) {all = []}     [] []               = []
  (<+>) {all = _ :: _} (v :: vs) (w :: ws) = (v <+> w) :: (vs <+> ws)

public export
(all : NP (Monoid . f) ks) => Monoid (NP' k f ks) where
  neutral {all = []}     = []
  neutral {all = _ :: _} = neutral :: neutral

private
consInjective : Data.SOP.NP.(::) a b = Data.SOP.NP.(::) c d -> (a = c, b = d)
consInjective Refl = (Refl, Refl)

public export
(all : NP (DecEq . f) ks) => DecEq (NP' k f ks) where
  decEq {all = []}     []        []        = Yes Refl
  decEq {all = _::_} (v::vs) (w::ws) with (decEq v w)
    decEq {all = _::_} (v::vs) (w::ws) | (No contra) =
      No $ contra . fst . consInjective
    decEq {all = _::_} (v::vs) (v::ws) | (Yes Refl) with (decEq vs ws)
      decEq {all = _::_} (v::vs) (v::vs) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq {all = _::_} (v::vs) (v::ws) | (Yes Refl) | (No contra) =
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

HPureTest : NP Maybe [String,Int]
HPureTest = hpure Nothing

CPureNeutralTest : NP I [String,String]
CPureNeutralTest = hcpure Monoid neutral

Person : (f : Type -> Type) -> Type
Person f = NP f [String,Int]

toPersonMaybe : Person I -> Person Maybe
toPersonMaybe = hmap Just

personShowValues : Person I -> Person (K String)
personShowValues = hcmap Show show

emptyPerson : Person Maybe
emptyPerson = hpure Nothing

fooPerson : Person (K String)
fooPerson = hconst "foo"

Foo : (f : Type -> Type) -> Type
Foo f = NP f [String,String,List Int]

neutralFoo : Foo I
neutralFoo = hcpure Monoid neutral

update : forall a . Maybe a -> I a -> I a
update (Just a) _ = a
update Nothing  a = a

updatePerson : Person (\a => a -> a)
updatePerson = hmap update [Just "foo", Nothing]

updatedPerson : Person I
updatedPerson = hap updatePerson ["bar",12]
