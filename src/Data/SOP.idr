module Data.SOP

--------------------------------------------------------------------------------
--          Type-level Utilities
--------------------------------------------------------------------------------

||| Type-level identity function.
public export
I : Type -> Type
I v = v

||| Type-level constant function.
public export
K : Type -> k -> Type
K t _ = t

public export
All : (f : k -> Type) -> (ks : List k) -> Type
All f []        = ()
All f (k :: ks) = (f k, All f ks)

--------------------------------------------------------------------------------
--          NP
--------------------------------------------------------------------------------

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
data NP : (f : k -> Type) -> (ks : List k) -> Type where
  Nil  : NP f []
  (::) : {0 t : k} -> (v : f t) -> (vs : NP f ks) -> NP f (t :: ks)

public export
hd : NP f (k :: ks) -> f k
hd (v :: _) = v

public export
tl : NP f (k :: ks) -> NP f ks
tl (_ :: vs) = vs

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

--------------------------------------------------------------------------------
--          Examples and Tests
--------------------------------------------------------------------------------

ex1 : NP I [Char,Bool]
ex1 = ['c',True]

ex2 : NP Maybe [Int,Int,Int]
ex2 = [Nothing,Nothing,Just 2]

ex3 : NP (K String) [Char,Bool,Int]
ex3 = ["Hello","World","!"]

eqTest1 : Data.SOP.ex1 == Data.SOP.ex1 = True
eqTest1 = Refl

eqTest2 : Data.SOP.ex1 == ['x',False] = False
eqTest2 = Refl

ordTest1 : compare Data.SOP.ex1 Data.SOP.ex1 = EQ
ordTest1 = Refl

ordTest2 : compare Data.SOP.ex1 ['x',False] = LT
ordTest2 = Refl
