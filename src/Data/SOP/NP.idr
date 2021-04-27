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
||| Note: `NP_` takes an additional type parameter `k` to simulate
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
data NP_ : (k : Type) -> (f : k -> Type) -> (ks : List k) -> Type where
  Nil  : NP_ k f []
  (::) : (v : f t) -> (vs : NP_ k f ks) -> NP_ k f (t :: ks)

||| Type alias for `NP_` with type parameter `k` being
||| implicit. This reflects the kind-polymorphic data type
||| in Haskell.
public export
NP : {k : Type} -> (f : k -> Type) -> (ks : List k) -> Type
NP = NP_ k

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
foldrNP : (fun : elem -> Lazy acc -> acc) -> Lazy acc -> NP (K elem) ks -> acc
foldrNP _   acc []        = acc
foldrNP fun acc (v :: vs) = fun v (foldrNP fun acc vs)

||| Specialization of `hsequence`
public export
sequenceNP : Applicative g => NP (\a => g (f a)) ks -> g (NP f ks)
sequenceNP []        = pure []
sequenceNP (v :: vs) = [| v :: sequenceNP vs |]

||| Specialization of `hcollapse`
public export
collapseNP : NP (K a) ks -> List a
collapseNP []        = []
collapseNP (v :: vs) = v :: collapseNP vs

--------------------------------------------------------------------------------
--          Core Functions
--------------------------------------------------------------------------------

||| Returns the head of a non-empty n-ary product
public export
hd : NP f (k :: ks) -> f k
hd (v :: _) = v

||| Returns the tail of a non-empty n-ary product
public export
tl : NP f (k :: ks) -> NP f ks
tl (_ :: vs) = vs

||| Creates a homogeneous n-ary product of the given
||| shape by repeatedly applying a function to a seed value.
public export
unfoldNP : NP f ks -> (s -> (s,a)) -> s -> NP (K a) ks
unfoldNP []       _ _ = []
unfoldNP (_ :: t) g s = let (s2,v) = g s
                         in v :: unfoldNP t g s

||| Like `unfoldNP` but takes the shape from the implicit
||| list of types.
public export
unfold : {ks : _} -> (s -> (s,a)) -> s -> NP (K a) ks
unfold = unfoldNP (pureNP ())

||| Creates a homogeneous n-ary product of the given
||| shape using an initial value and a function for
||| generating the next value.
public export
iterateNP : NP f ks -> (a -> a) -> a -> NP (K a) ks
iterateNP np f = unfoldNP np (\v => (f v, v))

||| Like `iterate` but takes the shape from the implicit
||| list of types.
public export
iterate : {ks : _} -> (a -> a) -> a -> NP (K a) ks
iterate = iterateNP (pureNP ())

||| A projection of an n-ary product p extracts the
||| value of p at a certain position.
public export
0 Projection : (f : k -> Type) -> (ks : List k) -> (v : k) -> Type
Projection f ks v = NP f ks -> f v

||| The set of projections of an n-ary product `NP f ks` can
||| itself be wrapped in an n-ary product of the same shape.
public export
projections : {ks : _} -> NP (Projection f ks) ks
projections {ks = []}       = []
projections {ks = (_ :: _)} = hd :: mapNP (. tl) projections

--------------------------------------------------------------------------------
--          Accessing Values
--------------------------------------------------------------------------------

||| Access the first element of the given type in
||| an n-ary product
public export
get : (0 t : k) -> {auto prf : Elem t ks} -> NP_ k f ks -> f t
get t {prf = Here}    (v :: _) = v
get t {prf = There _} (_ :: vs) = get t vs

--------------------------------------------------------------------------------
--          Modifying Values
--------------------------------------------------------------------------------

||| Modify a single element of the given type
||| in an n-ary product, thereby possibly changing the
||| types of stored values.
public export
modify :  (fun : f t -> f t')
       -> {auto prf : UpdateOnce t t' ks ks'}
       -> NP_ k f ks
       -> NP_ k f ks'
modify fun {prf = UpdateHere}    (v :: vs) = fun v :: vs
modify fun {prf = UpdateThere _} (v :: vs) = v :: modify fun vs

||| Modify a single element of the given type
||| in an n-ary product by applying an effectful
||| function.
|||
||| This is the effectful version of `modify`.
public export
modifyF :  Functor g
        => (fun : f t -> g (f t'))
        -> {auto prf : UpdateOnce t t' ks ks'}
        -> NP_ k f ks
        -> g (NP_ k f ks')
modifyF fun {prf = UpdateHere}    (v :: vs) = (:: vs) <$> fun v
modifyF fun {prf = UpdateThere _} (v :: vs) = (v ::)  <$> modifyF fun vs

||| Modify several elements of the given type
||| in an n-ary product, thereby possibly changing the
||| types of stored values.
public export
modifyMany :  (fun : f t -> f t')
           -> {auto prf : UpdateMany t t' ks ks'}
           -> NP_ k f ks
           -> NP_ k f ks'
modifyMany f {prf = UMNil}        []      = []
modifyMany f {prf = UMConsSame x} (v::vs) = f v :: modifyMany f vs
modifyMany f {prf = UMConsDiff x} (v::vs) = v   :: modifyMany f vs

||| Modify several elements of the given type
||| in an n-ary product by applying an effectful function.
|||
||| This is the effectful version of `modifyMany`.
public export
modifyManyF :  Applicative g
            => (fun : f t -> g (f t'))
            -> {auto prf : UpdateMany t t' ks ks'}
            -> NP_ k f ks
            -> g (NP_ k f ks')
modifyManyF f {prf = UMNil}        []      = pure []
modifyManyF f {prf = UMConsSame x} (v::vs) = [| f v :: modifyManyF f vs |]
modifyManyF f {prf = UMConsDiff x} (v::vs) = (v ::) <$> modifyManyF f vs

||| Replaces the first element of the given type
||| in an n-ary product, thereby possibly changing the
||| types of stored values.
public export %inline
setAt :  (0 t : k)
      -> (v' : f t')
      -> {auto prf : UpdateOnce t t' ks ks'}
      -> NP_ k f ks
      -> NP_ k f ks'
setAt t v' = modify {t = t} (const v')

||| Replaces several elements of the given type
||| in an n-ary product, thereby possibly changing the
||| types of stored values.
public export %inline
setAtMany :  (0 t : k)
          -> (v' : f t')
          -> {auto prf : UpdateMany t t' ks ks'}
          -> NP_ k f ks
          -> NP_ k f ks'
setAtMany t v' = modifyMany {t = t} (const v')

||| Alias for `setAt` for those occasions when
||| Idris cannot infer the type of the new value.
public export %inline
setAt' :  (0 t  : k)
       -> (0 t' : k)
       -> (v' : f t')
       -> {auto prf : UpdateOnce t t' ks ks'}
       -> NP_ k f ks
       -> NP_ k f ks'
setAt' t _ v' np = setAt t v' np

||| Alias for `setAtMany` for those occasions when
||| Idris cannot infer the type of the new value.
public export %inline
setAtMany' :  (0 t  : k)
           -> (0 t' : k)
           -> (v' : f t')
           -> {auto prf : UpdateMany t t' ks ks'}
           -> NP_ k f ks
           -> NP_ k f ks'
setAtMany' t _ v' np = setAtMany t v' np

--------------------------------------------------------------------------------
--          Narrowing and expanding products
--------------------------------------------------------------------------------

||| Extracts a subset of values from an n-ary product.
||| The values must appear in the same order in both lists.
public export
narrow : NP f ks -> {auto prf: Sublist ks' ks} -> NP f ks'
narrow x         {prf = SLNil}    = []
narrow (v :: vs) {prf = SLSame y} = v :: narrow vs
narrow (_ :: vs) {prf = SLDiff y} = narrow vs

||| Appends two n-ary products.
public export
append : NP f ks -> NP f ks' -> NP f (ks ++ ks')
append []        y = y
append (v :: vs) y = v :: append vs y

||| Expands an n-ary product by filling missing
||| values with the given default-generating function.
public export
expand :  {ks' : List k}
       -> (forall k . f k)
       -> NP f ks
       -> {auto prf : Sublist ks ks'}
       -> NP f ks'
expand f []                         = pureNP f
expand f (v :: vs) {prf = SLSame x} = v :: expand f vs
expand f vs        {prf = SLDiff x} = f :: expand f vs

||| Expands an n-ary product by filling missing
||| values with the given default-generating function.
|||
||| This is the constrained version of `expand`.
public export
cexpand :  (0 c : k -> Type)
        -> (cs : NP c ks')
        => (forall k . c k => f k)
        -> {auto prf : Sublist ks ks'}
        -> NP_ k f ks
        -> NP_ k f ks'
cexpand c {cs = []}   f []                         = []
cexpand c {cs = _::_} f []                         = f :: cexpand c f []
cexpand c {cs = _::_} f (v :: vs) {prf = SLSame x} = v :: cexpand c f vs
cexpand c {cs = _::_} f vs        {prf = SLDiff x} = f :: cexpand c f vs

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
HPure k (List k) (NP_ k) where hpure  = pureNP

public export %inline
HFunctor k (List k) (NP_ k) where hmap  = mapNP

public export %inline
HAp k (List k) (NP_ k) (NP_ k) where hap = hapNP

public export %inline
HFold k (List k) (NP_ k) where
  hfoldl = foldlNP
  hfoldr = foldrNP

public export %inline
HCollapse k (List k) (NP_ k) List where hcollapse = collapseNP

public export %inline
HSequence k (List k) (NP_ k) where hsequence = sequenceNP

public export
(all : NP (Eq . f) ks) => Eq (NP_ k f ks) where
  (==) {all = []}     [] []               = True
  (==) {all = _ :: _} (v :: vs) (w :: ws) = v == w && vs == ws

public export
(all : NP (Ord . f) ks) => Ord (NP_ k f ks) where
  compare {all = []}     [] []               = EQ
  compare {all = _ :: _} (v :: vs) (w :: ws) = compare v w <+> compare vs ws

public export
(all : NP (Semigroup . f) ks) => Semigroup (NP_ k f ks) where
  (<+>) {all = []}     [] []               = []
  (<+>) {all = _ :: _} (v :: vs) (w :: ws) = (v <+> w) :: (vs <+> ws)

public export
(all : NP (Monoid . f) ks) => Monoid (NP_ k f ks) where
  neutral {all = []}     = []
  neutral {all = _ :: _} = neutral :: neutral

public export
(all : NP (Show . f) ks) => Show (NP_ k f ks) where
  show =  dispStringList . hcollapse . hcmap (Show . f) show

private
consInjective : Data.SOP.NP.(::) a b = Data.SOP.NP.(::) c d -> (a = c, b = d)
consInjective Refl = (Refl, Refl)

public export
(all : NP (DecEq . f) ks) => DecEq (NP_ k f ks) where
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

seqMaybe : NP Maybe [Int,String] -> Maybe (NP I [Int,String])
seqMaybe = hsequence

htraverseEx : NP (Either String) [Int,String] -> Maybe (NP I [Int,String])
htraverseEx = htraverse (either (const Nothing) Just)

interface Read a where
  read : String -> Maybe a

hctraverseEx : NP Read [Int,String] => NP (K String) [Int,String] -> Maybe (NP I [Int,String])
hctraverseEx = hctraverse Read read

subproductEx : NP I [Int,String,Bool,Maybe Bool] -> NP I [Int,Bool]
subproductEx np = narrow np
