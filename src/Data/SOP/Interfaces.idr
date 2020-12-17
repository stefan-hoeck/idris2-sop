||| This module provides interfaces similar to `Applicative`
||| and `Traversable` for heterogeneous container types.
||| We distinguish between two types of containers: Product
||| types hold all their values at once, while sum types
||| represent a choice: A generalization of `Either`.
|||
||| The core data types in this library are indexed over a
||| container (typically a List or List of Lists) of values
||| of type `k` plus a type-level function `f` of type `k -> Type`.
||| The values of the container index together with `f` determine
||| the types of values at each position in the
||| heterogeneous product or sum, while the shape of container
||| indices mirror the shape of the corresponding product types.
||| 
||| The interfaces in this module allow us to create
||| hetereogeneous containers from sufficiently general functions
||| (`HPure`), use unary functions to change the context of
||| values in a heterogeneous container (`HFunctor`),
||| collapse heterogeneous containers into a single value (`HFoldable`)
||| and run an effectful computation over all values in
||| a heterogeneous container (`HSequence`).
|||
||| In addition, `HFunctor` can be generalized to arbitrary
||| n-ary functions (`HAp`). However, this case is special in that only
||| the last argument of such a function can be a sum type
||| while all other arguments have to be product types.
||| This makes sense, since when combining values of two sum types,
||| we typically cannot guarantee that the values point at
||| same choice and are therefore compatible.
|||
||| Implementation notes:
|||
||| For many of the functions in this module, there is a constrained
||| version taking an implicit heterogeneous product holding
||| the desired implementations. Since Idris2 uses the same
||| mechanism for resolving interface constraints and auto implicits,
||| we do not need an additional structure or interface
||| for these constraints.
||| The disadvantage of this is, that we more often have to explicitly
||| pattern match on these constraint products in order for Idris2
||| to know where to look for implementations.
module Data.SOP.Interfaces

import Data.SOP.Utils

%default total

||| A heterogeneous container indexed over a container type `l`
||| holding values of type `k`.
%inline
public export
HCont : (k : Type) -> (l : Type) -> Type
HCont k l = (k -> Type) -> l -> Type

--------------------------------------------------------------------------------
--          HPure
--------------------------------------------------------------------------------

||| This interface allows a heterogenous product to be filled
||| with values, given a function which produce values of
||| every possible type required.
|||
||| @ k kind of Types in a heterogeneous container's  type level code
|||
||| @ l kind of container used to describe a heterogeneous containr's type
|||     level code
|||
||| @ p the heterogeneous sum or product
public export
interface HPure k l (0 p : HCont k l) | p where

  ||| Creates a heterogeneous product by using the given functio
  ||| to produce values.
  |||
  ||| ```idris example
  ||| Person : (f : Type -> Type) -> Type
  ||| Person f = NP f [String,Int]
  |||
  ||| emptyPerson : Person Maybe
  ||| emptyPerson = hpure Nothing
  ||| ```
  hpure :  {0 f : k -> Type} -> {ks : l}
        -> (forall a . f a) -> p f ks

||| Alias for `hpure empty`.
|||
||| ```idris example
||| Person : (f : Type -> Type) -> Type
||| Person f = NP f [String,Int]
|||
||| emptyPerson : Person Maybe
||| emptyPerson = empty
||| ```
public export
hempty : {ks : _} -> Alternative f => HPure Type l p => p f ks
hempty = hpure empty

||| Fills a heterogeneous structure with a constant value
||| in the (K a) functor.
|||
||| ```idris example
||| Person : (f : Type -> Type) -> Type
||| Person f = NP f [String,Int]
|||
||| fooPerson : Person (K String)
||| fooPerson = hconst "foo"
||| ```
public export
hconst : {ks : _} -> HPure k l p => (v : a) -> p (K a) ks
hconst v = hpure v


--------------------------------------------------------------------------------
--          HFunctor
--------------------------------------------------------------------------------

||| A higher kinded functor allowing us to change the
||| wrapper type or context of an n-ary sum or product.
|||
||| @ k kind of Types in a heterogeneous container's  type level code
|||
||| @ l kind of container used to describe a heterogeneous containr's type
|||     level code
|||
||| @ p the actual heterogeneous container
public export
interface HFunctor k l (0 p : HCont k l) | p where

  ||| Maps the given function over all values in a
  ||| heterogeneous container, thus changing the context
  ||| of all of its values.
  |||
  ||| @ fun maps values in a heterogeneous container to a new context
  |||
  ||| @ p   the heterogeneous container, over which `fun` is mapped.
  |||
  ||| ```idris example
  ||| Person : (f : Type -> Type) -> Type
  ||| Person f = NP f [String,Int]
  |||
  ||| toPersonMaybe : Person I -> Person Maybe
  ||| toPersonMaybe = hmap Just
  ||| ```
  hmap :  {0 f,g : k -> Type}
       -> {0 ks : l}
       -> (fun : forall a . f a -> g a)
       -> p f ks
       -> p g ks

||| Alias for `hmap`
public export %inline
hliftA : HFunctor k l p => (forall a . f a -> g a) -> p f ks -> p g ks
hliftA = hmap

||| Like `hpure` but using a constrained function for
||| generating values. Since Idris is able to provide
||| the required constraints
||| already wrapped in a container of the correct
||| shape, this is actually a derivative of `HFunctor` and not
||| `HPure`. This has interesting consequences for sum
||| types, for which this function is available as well.
||| Since Idris has to choose a value of the sum
||| itself, it will use the first possibility it
||| can fill with the requested constraints.
|||
||| In the first example below, Idris generates the value
||| `MkSOP (Z ["","",[]])`. However, if the first choice does
||| not have a Monoid instance, Idris faithfully chooses the
||| next working possibility. In the second example,
||| the result is `MkSOP (S (Z [[],[]]))`:
|||
||| ```idris example
||| neutralFoo : SOP I [[String,String,List Int],[Int]]
||| neutralFoo = hcpure Monoid neutral
|||
||| neutralBar : SOP I [[String,Int,List Int],[List String, List Int]]
||| neutralBar = hcpure Monoid neutral
||| ```
|||
||| @ c   erased function argument to specify the constraint
|||       to use
|||
||| @ fun generates values depending on the availability of
|||       a constraint
public export
hcpure :  HFunctor k l p
       => (0 c : k -> Type)
       -> (cs : p c ks)
       => (fund : forall a . c a => f a)
       -> p f ks
hcpure _ {cs} fun = hmap (\_ => fun) cs

--------------------------------------------------------------------------------
--          HAp
--------------------------------------------------------------------------------

||| Like `Applicative`, this interface allows to
||| map arbitrary n-ary Rank-2 functions over
||| heterogeneous data structures of the same shape.
||| However, in order to support products as well as sum types
||| all arguments except the last one have to be products
||| indexed over the same container as the last argument.
|||
||| @ k kind of Types in a heterogeneous container's  type level code
|||
||| @ l kind of container used to describe a heterogeneous containr's type
|||     level code
|||
||| @ q heterogeneous product related to `p`. For product types,
|||     this is the same as `p`, for sum types it is the corresponding
|||     product type.
|||
||| @ p the actual heterogeneous container (sum or product)
public export
interface HFunctor k l q => HFunctor k l p => HAp k l q p | p where

  ||| Higher kinded equivalent to `(<*>)`.
  |||
  ||| Applies wrapped functions in the product
  ||| container to the corresponding values in the
  ||| second container.
  |||
  ||| @ q product holding unary Rank-2 functions.
  |||
  ||| @ p sum or product to whose values the functions in `q` should
  |||     be applied
  |||
  ||| ```idris example
  ||| hapTest : SOP Maybe [[String,Int]] -> SOP I [[String,Int]]
  ||| hapTest = hap (MkPOP $ [[fromMaybe "foo", const 12]])
  ||| ```
  hap :  {0 f,g : k -> Type}
      -> {0 ks : l}
      -> q (\a => f a -> g a) ks
      -> p f ks
      -> p g ks

||| Higher kinded version of `liftA2`.
||| This is a generalization of `hliftA` to binary
||| functions.
public export
hliftA2 :  HAp k l q p
        => (forall a . f a -> g a -> h a)
        -> q f ks
        -> p g ks
        -> p h ks
hliftA2 fun fs gs  = hliftA fun fs `hap` gs

||| Higher kinded version of `liftA3`.
||| This is a generalization of `hliftA` to ternary
||| functions.
public export
hliftA3 :  (HAp k l q q, HAp k l q p)
        => (forall a . f a -> g a -> h a -> i a)
        -> q f ks
        -> q g ks
        -> p h ks
        -> p i ks
hliftA3 fun fs gs hs = hliftA2 fun fs gs `hap` hs

||| Higher kinded version of `liftA4`.
||| This is a generalization of `hliftA` to quartenary
||| functions.
public export
hliftA4 :  (HAp k l q q, HAp k l q p)
        => (forall a . f a -> g a -> h a -> i a -> j a)
        -> q f ks
        -> q g ks
        -> q h ks
        -> p i ks
        -> p j ks
hliftA4 fun fs gs hs is = hliftA3 fun fs gs hs `hap` is

||| Like `hmap` but uses a constrained function.
|||
||| @ c   constraint used to convert values
|||
||| @ fun constrained function for converting values to
|||       a new context
|||
||| ```idris example
||| showValues : NP I [String,Int] -> NP (K String) [String,Int]
||| showValues = hcmap Show show
||| ```
public export
hcmap :  HAp k l q p
      => (0 c : k -> Type)
      -> (cs : q c ks)
      => (fun : forall a . c a => f a -> g a)
      -> p f ks
      -> p g ks
hcmap _ {cs} fun = hliftA2 (\_ => fun) cs 

||| Alias for `hcmap`
public export %inline
hcliftA :  HAp k l q p
        => (0 c : k -> Type)
        -> q c ks
        => (fun : forall a . c a => f a -> g a)
        -> p f ks
        -> p g ks
hcliftA = hcmap

||| Like `hliftA2` but with a constrained function.
public export %inline
hcliftA2 :  (HAp k l q q, HAp k l q p)
         => (0 c : k -> Type)
         -> (cs : q c ks)
         => (fun : forall a . c a => f a -> g a -> h a)
         -> q f ks
         -> p g ks
         -> p h ks
hcliftA2 _ {cs} fun = hliftA3 (\_ => fun) cs

||| Like `hliftA3` but with a constrained function.
public export %inline
hcliftA3 :  (HAp k l q q, HAp k l q p)
         => (c : k -> Type)
         -> (cs : q c ks)
         => (fun : forall a . c a => f a -> g a -> h a -> i a)
         -> q f ks
         -> q g ks
         -> p h ks
         -> p i ks
hcliftA3 _ {cs} fun = hliftA4 (\_ => fun) cs

--------------------------------------------------------------------------------
--          HFold
--------------------------------------------------------------------------------

public export
interface HFold k l (0 p : HCont k l) | p where

  ||| Strict fold over a heterogeneous sum or product
  ||| parameterized by the constant functor (and thus being actually
  ||| a homogeneous sum or product).
  hfoldl : {0 ks : l} -> (acc -> elem -> acc) -> acc -> p (K elem) ks -> acc

  ||| Lazy fold over a heterogeneous sum or product
  ||| parameterized by the constant functor (and thus being actually
  ||| a homogeneous sum or product).
  hfoldr :  {0 ks : l}
         -> (elem -> Lazy acc -> acc) -> Lazy acc -> p (K elem) ks -> acc


||| Alias for `hfoldl (<+>) neutral`.
public export
hconcat : (Monoid m, HFold k l p) => p (K m) ks -> m
hconcat = hfoldl (<+>) neutral

||| Alias for `hconcat . hmap fun`
public export
hconcatMap :  (Monoid m, HFunctor k l p, HFold k l p)
           => (fun : forall a . f a -> m) -> p f ks -> m
hconcatMap fun = hconcat . hmap fun

||| Alias for `hconcat . hcmap c fun`
public export
hcconcatMap :  (Monoid m, HAp k l q p, HFold k l p)
            => (0 c : k -> Type)
            -> q c ks
            => (fun : forall a . c a => f a -> m)
            -> p f ks
            -> m
hcconcatMap c fun = hconcat . hcmap c fun

||| Generalization of `sequence_` to heterogeneous containers.
||| 
||| Alias for `hfoldl (*>) (pure ())`.
public export
hsequence_ : (Applicative g, HFold k l p) => p (K (g ())) ks -> g ()
hsequence_ = hfoldl (*>) (pure ())

||| Generalization of `traverse_` to heterogeneous containers.
||| 
||| Alias for `hsequence_ . hmap fun`.
public export
htraverse_ :  (Applicative g, HFold k l p, HFunctor k l p)
           => (forall a . f a -> g ()) -> p f ks -> g ()
htraverse_ fun = hsequence_ . hmap fun

||| Generalization of `for_` to heterogeneous containers.
public export
hfor_ :  (Applicative g, HFold k l p, HFunctor k l p)
      => p f ks -> (forall a . f a -> g ()) -> g ()
hfor_ = flip htraverse_

||| Generalization of `and` to heterogeneous containers.
public export
hand : HFold k l p => p (K Bool) ks -> Bool
hand = hfoldr (\a,b => a && b) True

||| Generalization of `toList` to heterogeneous containers.
export
htoList : (HFunctor k l p, HFold k l p) => p (K a) ks -> List a
htoList = hconcatMap pure

||| Generalization of `or` to heterogeneous containers.
export
hor : HFold k l p => p (K Bool) ks -> Bool
hor = hfoldr (\a,b => a || b) False

||| Generalization of `all` to heterogeneous containers.
export
hall :   (HFunctor k l p, HFold k l p)
      => (forall a . f a -> Bool)
      -> p f ks -> Bool
hall fun = hand . hmap fun

||| Generalization of `any` to heterogeneous containers.
export
hany :  (HFunctor k l p, HFold k l p)
     => (forall a . f a -> Bool)
     -> p f ks -> Bool
hany fun = hor . hmap fun

||| Generalization of `choice` to heterogeneous containers.
export
hchoice : HFold k l p => Alternative f =>  p (K $ f a) ks -> f a
hchoice = hfoldr (\a,b => a <|> b) empty

--------------------------------------------------------------------------------
--          HSequence
--------------------------------------------------------------------------------

||| Sequencing of applicative effects over a heterogeneous
||| container.
public export
interface HSequence k l (0 p : HCont k l) | p where

  ||| Given a heterogeneous containers holding values
  ||| wrapped in effect `g`, sequences applications of
  ||| `g` to the outside of the heterogeneous container.
  |||
  ||| ```idris example
  ||| seqMaybe : NP Maybe [Int,String] -> Maybe (NP I [Int,String])
  ||| seqMaybe = hsequence
  ||| ```
  hsequence :  {0 ks : l}
            -> {0 f : k -> Type}
            -> Applicative g
            => p (\a => g (f a)) ks
            -> g (p f ks)

||| Traverses a heterogeneous container by applying effectful
||| function `fun`.
|||
||| ```idris example
||| htraverseEx : NP (Either String) [Int,String] -> Maybe (NP I [Int,String])
||| htraverseEx = htraverse (either (const Nothing) Just)
||| ```
export
htraverse :  {0 f,f' : k -> Type}
          -> (Applicative g, HFunctor k l p, HSequence k l p)
          => (fun : forall a . f a -> g (f' a))
          -> p f ks
          -> g (p f' ks)
htraverse fun = hsequence . hmap fun

||| Flipped version of `htraverse`.
export
hfor :  {0 f,f' : k -> Type}
     -> (Applicative g, HFunctor k l p, HSequence k l p)
     => p f ks
     -> (forall a . f a -> g (f' a))
     -> g (p f' ks)
hfor = flip htraverse

||| Constrained version of `htraverse`.
|||
||| ```idris example
||| interface Read a where
|||   read : String -> Maybe a
||| 
||| hctraverseEx : NP Read [Int,String] =>
|||                NP (K String) [Int,String] -> Maybe (NP I [Int,String])
||| hctraverseEx = hctraverse Read read
||| ```
export
hctraverse :  {0 f,f' : k -> Type}
           -> (Applicative g, HAp k l q p, HSequence k l p)
           => (0 c : k -> Type)
           -> (cs : q c ks)
           => (forall a . c a => f a -> g (f' a))
           -> p f ks
           -> g (p f' ks)
hctraverse c fun = hsequence . hcmap c fun

||| Flipped version of `hctraverse`.
export
hcfor :  {0 f,f' : k -> Type}
      -> (Applicative g, HAp k l q p, HSequence k l p)
      => (0 c : k -> Type)
      -> (cs : q c ks)
      => p f ks
      -> (forall a . c a => f a -> g (f' a))
      -> g (p f' ks)
hcfor c = flip (hctraverse c)

--------------------------------------------------------------------------------
--          HCollapse
--------------------------------------------------------------------------------

||| Collapsing a heterogeneous container to a homogeneous one
||| of the same shape.
public export
interface HCollapse k l (0 p : HCont k l) (0 collapseTo : Type -> Type) | p where

  ||| A heterogeneous container over constant functor `K a` is
  ||| actually a homogeneous one holding only values of type `a`.
  ||| This function extracts the wrapped values into a homogeneous
  ||| one of the same size and shape.
  hcollapse : {0 a : Type} -> {0 ks : l} -> p (K a) ks -> collapseTo a
