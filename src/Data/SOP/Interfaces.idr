module Data.SOP.Interfaces

import Data.SOP.Utils

%default total

--------------------------------------------------------------------------------
--          HFunctor
--------------------------------------------------------------------------------

public export
interface HFunctor (p : (k : Type) -> (k -> Type) -> List k -> Type) where 
  hmap : (fun : forall a . f a -> g a) -> p k f ks -> p k g ks

  hcmap :  (c : k -> Type)
        -> All c ks
        => (fun : forall a . c a => f a -> g a)
        -> p k f ks
        -> p k g ks

public export %inline
hliftA : HFunctor p => (forall a . f a -> g a) -> p k f ks -> p k g ks
hliftA = hmap

public export %inline
hcliftA :  HFunctor p
        => (c : k -> Type)
        -> All c ks
        => (fun : forall a . c a => f a -> g a)
        -> p k f ks
        -> p k g ks
hcliftA = hcmap

--------------------------------------------------------------------------------
--          HPure
--------------------------------------------------------------------------------

public export
interface HPure (p : (k : Type) -> (k -> Type) -> List k -> Type) where
  hpure : {ks : _} -> (forall a . f a) -> p k f ks

  cpure :  {ks : _}
        -> (c : k -> Type)
        -> All c ks
        => (forall a . c a => f a)
        -> p k f ks

public export
hempty : {ks : _} -> Alternative f => HPure p => p Type f ks
hempty = hpure empty

public export
hconst : {ks : _} -> HPure p => (v : a) -> p k (K a) ks
hconst v = hpure v

--------------------------------------------------------------------------------
--          HAp
--------------------------------------------------------------------------------

public export
interface HFunctor p => HPure p => HAp p where
  hap : p k (\a => f a -> g a) ks -> p k f ks -> p k g ks

public export
hliftA2 :  HAp p
        => (forall a . f a -> g a -> h a)
        -> p k f ks
        -> p k g ks
        -> p k h ks
hliftA2 fun fs gs  = hliftA fun fs `hap` gs

public export
hliftA3 :  HAp p
        => (forall a . f a -> g a -> h a -> i a)
        -> p k f ks
        -> p k g ks
        -> p k h ks
        -> p k i ks
hliftA3 fun fs gs hs = hliftA2 fun fs gs `hap` hs

public export %inline
hcliftA2 :  HAp p
         => (c : k -> Type)
         -> All c ks
         => (fun : forall a . c a => f a -> g a -> h a)
         -> p k f ks
         -> p k g ks
         -> p k h ks
hcliftA2 c fun fs gs = hcliftA c fun fs `hap` gs

public export %inline
hcliftA3 :  HAp p
         => (c : k -> Type)
         -> All c ks
         => (fun : forall a . c a => f a -> g a -> h a -> i a)
         -> p k f ks
         -> p k g ks
         -> p k h ks
         -> p k i ks
hcliftA3 c fun fs gs hs = hcliftA2 c fun fs gs `hap` hs

--------------------------------------------------------------------------------
--          HFold
--------------------------------------------------------------------------------

public export
interface HFold (p : (k : Type) -> (k -> Type) -> List k -> Type) where
  hfoldl : (acc -> elem -> acc) -> acc -> p k (K elem) ks -> acc

  hfoldr : (elem -> acc -> acc) -> acc -> p k (K elem) ks -> acc


public export
hconcat : (Monoid m, HFold p) => p k (K m) ks -> m
hconcat = hfoldl (<+>) neutral

public export
hconcatMap :  (Monoid m, HFunctor p, HFold p)
           => (forall a . f a -> m) -> p k f ks -> m
hconcatMap fun = hconcat . hmap fun

public export
hcconcatMap :  (Monoid m, HFunctor p, HFold p)
            => (c : k -> Type)
            -> All c ks
            => (forall a . c a => f a -> m)
            -> p k f ks
            -> m
hcconcatMap c fun = hconcat . hcmap c fun

public export
hsequence_ : (Applicative g, HFold p) => p k (K (g ())) ks -> g ()
hsequence_ = hfoldl (*>) (pure ())

public export
htraverse_ :  (Applicative g, HFold p, HFunctor p)
           => (forall a . f a -> g ()) -> p k f ks -> g ()
htraverse_ fun = hsequence_ . hmap fun

public export
hfor_ :  (Applicative g, HFold p, HFunctor p)
      => p k f ks -> (forall a . f a -> g ()) -> g ()
hfor_ = flip htraverse_

public export
hand : HFold p => p k (K Bool) ks -> Bool
hand = hfoldl (\a,b => a && b) True

export
htoList : (HAp p, HFold p) => p k (K a) ks -> List a
htoList = hconcatMap pure

export
hor : HFold p => p k (K Bool) ks -> Bool
hor = hfoldl (\a,b => a || b) False

export
hall : (HFunctor p, HFold p) => (forall a . f a -> Bool) -> p k f ks -> Bool
hall fun = hand . hmap fun

export
hany : (HFunctor p, HFold p) => (forall a . f a -> Bool) -> p k f ks -> Bool
hany fun = hor . hmap fun

--------------------------------------------------------------------------------
--          HSequence
--------------------------------------------------------------------------------

public export
interface HSequence (p : (k : Type) -> (k -> Type) -> List k -> Type) where
  hsequence : Applicative g => p k (\a => g (f a)) ks -> g (p k f ks)

export
htraverse :  (Applicative g, HFunctor p, HSequence p)
          => (forall a . f a -> g (f a))
          -> p k f ks
          -> g (p k f ks)
htraverse fun = hsequence . hmap fun

export
hfor :  (Applicative g, HFunctor p, HSequence p)
     => p k f ks
     -> (forall a . f a -> g (f a))
     -> g (p k f ks)
hfor = flip htraverse

export
hctraverse :  (Applicative g, HFunctor p, HSequence p)
           => (c : k -> Type)
           -> All c ks
           => (forall a . c a => f a -> g (f a))
           -> p k f ks
           -> g (p k f ks)
hctraverse c fun = hsequence . hcmap c fun

export
hcfor :  (Applicative g, HFunctor p, HSequence p)
      => (c : k -> Type)
      -> All c ks
      => p k f ks
      -> (forall a . c a => f a -> g (f a))
      -> g (p k f ks)
hcfor c = flip (hctraverse c)
