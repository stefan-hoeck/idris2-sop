module Data.SOP.Interfaces

import Data.SOP.Utils

%default total

||| This interface is used to generate a list of
||| constraints for a container of type `l`
||| holding values of type `k` (determined by `l`).
|||
||| It is used whenever we want to apply a constrained
||| function to all values in an n-ary sum ord product.
public export
interface AllC k l | l where
  All : (f : k -> Type) -> l -> Type

-- Heterogeneous container
%inline
public export
HCont : (k : Type) -> (l : Type) -> Type
HCont k l = (0 _ : k -> Type) -> (0 _ : l) -> Type

--------------------------------------------------------------------------------
--          HFunctor
--------------------------------------------------------------------------------

||| A higher kinded functor allowing us to change the
||| wrapper type of an n-ary sum or product.
|||
||| @ k kind of Types in a heterogeneous container's  type level code
||| @ l kind of container used to describe a heterogeneous containr's type
|||     level code
||| @ p the actual heterogeneous container
|||
||| ```idris example
||| HFunctor k (List k) (NP' k) where
||| ```
public export
interface AllC k l => HFunctor k l (p : HCont k l) | p where
  ||| Maps the given function over all values in a
  ||| heterogeneous container, thus changing the wrappers
  ||| of all of its values.
  |||
  ||| @ fun maps all values in a heterogeneous container to
  |||       a new context
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

  ||| Like `hmap` but uses a constrained function.
  |||
  ||| @ c   constraint used to convert values
  ||| @ fun constrained function for converting values to
  |||       a new context
  |||
  ||| ```idris example
  ||| Person : (f : Type -> Type) -> Type
  ||| Person f = NP f [String,Int]
  |||
  ||| personShowValues : Person I -> Person (K String)
  ||| personShowValues = hcmap Show show
  ||| ```
  hcmap :  {0 f,g : k -> Type}  
        -> {0 ks : l}
        -> (c : k -> Type)
        -> All c ks
        => (fun : forall a . c a => f a -> g a)
        -> p f ks
        -> p g ks

||| Alias for `hmap`
public export %inline
hliftA : HFunctor k l p => (forall a . f a -> g a) -> p f ks -> p g ks
hliftA = hmap

||| Alias for `hcmap`
public export %inline
hcliftA :  HFunctor k l p
        => (c : k -> Type)
        -> All c ks
        => (fun : forall a . c a => f a -> g a)
        -> p f ks
        -> p g ks
hcliftA = hcmap

--------------------------------------------------------------------------------
--          HPure
--------------------------------------------------------------------------------

||| This interface allows a heterogenous container to be filled
||| with values, given function's which produce values of
||| every possible type required.
|||
||| See `HFunctor` for an explanation of the type parameters
||| used here.
public export
interface HFunctor k l p => HPure k l (p : HCont k l) | p where
  ||| Creates a heterogeneous container by generating values
  ||| using the given function.
  |||
  ||| ```idris example
  ||| Person : (f : Type -> Type) -> Type
  ||| Person f = NP f [String,Int]
  |||
  ||| emptyPerson : Person Maybe
  ||| emptyPerson = hpure Nothing
  ||| ```
  hpure : {0 f : k -> Type} -> {ks : l} -> (forall a . f a) -> p f ks

  ||| Like `hpure` but using a constrained function for
  ||| generating values.
  |||
  ||| ```idris example
  ||| Foo : (f : Type -> Type) -> Type
  ||| Foo f = NP f [String,String,List Int]
  |||
  ||| neutralFoo : Foo I
  ||| neutralFoo = hcpure Monoid neutral
  ||| ```
  hcpure :  {0 f : k -> Type} 
         -> {0 ks : l}
         -> (c : k -> Type) -> All c ks => (forall a . c a => f a) -> p f ks

||| Alias for `hpure empty`.
public export
hempty : {ks : _} -> Alternative f => HPure Type l p => p f ks
hempty = hpure empty

||| Fills a heterogeneous structure with a constant value
||| in the (K a) functor.
public export
hconst : {ks : _} -> HPure k l p => (v : a) -> p (K a) ks
hconst v = hpure v

--------------------------------------------------------------------------------
--          HAp
--------------------------------------------------------------------------------

||| Like `Applicative`, this interface allows to
||| map arbitrary n-ary Rank-2 functions over several
||| heterogeneous data structures.
|||
||| See `HFunctor` for an explanation of the type parameters
||| used here.
public export
interface HPure k l p => HAp k l p | p where
  ||| Higher kinded equivalent to `(<*>)`.
  |||
  ||| Applies wrapped functions in the first
  ||| container to the corresponding values in the
  ||| second container.
  hap :  {0 f,g : k -> Type}
      -> {0 ks : l}
      -> p (\a => f a -> g a) ks
      -> p f ks
      -> p g ks

||| Higher kinded version of `liftA2`.
public export
hliftA2 :  HAp k l p
        => (forall a . f a -> g a -> h a)
        -> p f ks
        -> p g ks
        -> p h ks
hliftA2 fun fs gs  = hliftA fun fs `hap` gs

||| Higher kinded version of `liftA3`.
public export
hliftA3 :  HAp k l p
        => (forall a . f a -> g a -> h a -> i a)
        -> p f ks
        -> p g ks
        -> p h ks
        -> p i ks
hliftA3 fun fs gs hs = hliftA2 fun fs gs `hap` hs

||| Like `hliftA2` but with a constrained function.
public export %inline
hcliftA2 :  HAp k l p
         => (c : k -> Type)
         -> All c ks
         => (fun : forall a . c a => f a -> g a -> h a)
         -> p f ks
         -> p g ks
         -> p h ks
hcliftA2 c fun fs gs = hcliftA c fun fs `hap` gs

||| Like `hliftA3` but with a constrained function.
public export %inline
hcliftA3 :  HAp k l p
         => (c : k -> Type)
         -> All c ks
         => (fun : forall a . c a => f a -> g a -> h a -> i a)
         -> p f ks
         -> p g ks
         -> p h ks
         -> p i ks
hcliftA3 c fun fs gs hs = hcliftA2 c fun fs gs `hap` hs

--------------------------------------------------------------------------------
--          HFold
--------------------------------------------------------------------------------

public export
interface HFold k l (p : HCont k l) | p where
  hfoldl : {0 ks : l} -> (acc -> elem -> acc) -> acc -> p (K elem) ks -> acc

  hfoldr : {0 ks : l} -> (elem -> acc -> acc) -> acc -> p (K elem) ks -> acc


public export
hconcat : (Monoid m, HFold k l p) => p (K m) ks -> m
hconcat = hfoldl (<+>) neutral

public export
hconcatMap :  (Monoid m, HFunctor k l p, HFold k l p)
           => (forall a . f a -> m) -> p f ks -> m
hconcatMap fun = hconcat . hmap fun

public export
hcconcatMap :  (Monoid m, HFunctor k l p, HFold k l p)
            => (c : k -> Type)
            -> All c ks
            => (forall a . c a => f a -> m)
            -> p f ks
            -> m
hcconcatMap c fun = hconcat . hcmap c fun

public export
hsequence_ : (Applicative g, HFold k l p) => p (K (g ())) ks -> g ()
hsequence_ = hfoldl (*>) (pure ())

public export
htraverse_ :  (Applicative g, HFold k l p, HFunctor k l p)
           => (forall a . f a -> g ()) -> p f ks -> g ()
htraverse_ fun = hsequence_ . hmap fun

public export
hfor_ :  (Applicative g, HFold k l p, HFunctor k l p)
      => p f ks -> (forall a . f a -> g ()) -> g ()
hfor_ = flip htraverse_

public export
hand : HFold k l p => p (K Bool) ks -> Bool
hand = hfoldl (\a,b => a && b) True

export
htoList : (HFunctor k l p, HFold k l p) => p (K a) ks -> List a
htoList = hconcatMap pure

export
hor : HFold k l p => p (K Bool) ks -> Bool
hor = hfoldl (\a,b => a || b) False

export
hall :   (HFunctor k l p, HFold k l p)
      => (forall a . f a -> Bool)
      -> p f ks -> Bool
hall fun = hand . hmap fun

export
hany :  (HFunctor k l p, HFold k l p)
     => (forall a . f a -> Bool)
     -> p f ks -> Bool
hany fun = hor . hmap fun

--------------------------------------------------------------------------------
--          HSequence
--------------------------------------------------------------------------------

public export
interface HSequence k l (p : HCont k l) | p where
  hsequence :  {0 ks : l}
            -> {0 f : k -> Type}
            -> Applicative g
            => p (\a => g (f a)) ks
            -> g (p f ks)

export
htraverse :  (Applicative g, HFunctor k l p, HSequence k l p)
          => (forall a . f a -> g (f a))
          -> p f ks
          -> g (p f ks)
htraverse fun = hsequence . hmap fun

export
hfor :  (Applicative g, HFunctor k l p, HSequence k l p)
     => p f ks
     -> (forall a . f a -> g (f a))
     -> g (p f ks)
hfor = flip htraverse

export
hctraverse :  (Applicative g, HFunctor k l p, HSequence k l p)
           => (c : k -> Type)
           -> All c ks
           => (forall a . c a => f a -> g (f a))
           -> p f ks
           -> g (p f ks)
hctraverse c fun = hsequence . hcmap c fun

export
hcfor :  (Applicative g, HFunctor k l p, HSequence k l p)
      => (c : k -> Type)
      -> All c ks
      => p f ks
      -> (forall a . c a => f a -> g (f a))
      -> g (p f ks)
hcfor c = flip (hctraverse c)
