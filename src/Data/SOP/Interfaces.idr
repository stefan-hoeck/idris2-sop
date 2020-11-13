module Data.SOP.Interfaces

import Data.SOP.Utils

%default total

public export
interface AllC k l | l where
  All : (f : k -> Type) -> l -> Type

public export
AllC k (List k) where
  All f [] = ()
  All f (k :: ks) = (f k, All f ks)

public export
AllC k (List $ List (k)) where
  All f []          = ()
  All f (ks :: kss) = (All f ks, All f kss)

--------------------------------------------------------------------------------
--          HFunctor
--------------------------------------------------------------------------------

public export
interface AllC k l => HFunctor k l (p : (k -> Type) -> l -> Type) | p where 
  hmap :  {0 f,g : k -> Type}
       -> {0 ks : l}
       -> (fun : forall a . f a -> g a)
       -> p f ks
       -> p g ks

  hcmap :  {0 f,g : k -> Type}  
        -> {0 ks : l}
        -> (c : k -> Type)
        -> All c ks
        => (fun : forall a . c a => f a -> g a)
        -> p f ks
        -> p g ks

public export %inline
hliftA : HFunctor k l p => (forall a . f a -> g a) -> p f ks -> p g ks
hliftA = hmap

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

public export
interface HFunctor k l p => HPure k l (p : (k -> Type) -> l -> Type) | p where
  hpure : {0 f : k -> Type} -> {ks : l} -> (forall a . f a) -> p f ks

  cpure :  {0 f : k -> Type} 
        -> {ks : l}
        -> (c : k -> Type) -> All c ks => (forall a . c a => f a) -> p f ks

public export
hempty : {ks : _} -> Alternative f => HPure Type l p => p f ks
hempty = hpure empty

public export
hconst : {ks : _} -> HPure k l p => (v : a) -> p (K a) ks
hconst v = hpure v

--------------------------------------------------------------------------------
--          HAp
--------------------------------------------------------------------------------

public export
interface HPure k l p => HAp k l p | p where
  hap :  {0 f,g : k -> Type}
      -> {0 ks : l}
      -> p (\a => f a -> g a) ks
      -> p f ks
      -> p g ks

public export
hliftA2 :  HAp k l p
        => (forall a . f a -> g a -> h a)
        -> p f ks
        -> p g ks
        -> p h ks
hliftA2 fun fs gs  = hliftA fun fs `hap` gs

public export
hliftA3 :  HAp k l p
        => (forall a . f a -> g a -> h a -> i a)
        -> p f ks
        -> p g ks
        -> p h ks
        -> p i ks
hliftA3 fun fs gs hs = hliftA2 fun fs gs `hap` hs

public export %inline
hcliftA2 :  HAp k l p
         => (c : k -> Type)
         -> All c ks
         => (fun : forall a . c a => f a -> g a -> h a)
         -> p f ks
         -> p g ks
         -> p h ks
hcliftA2 c fun fs gs = hcliftA c fun fs `hap` gs

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
interface HFold k l (p : (k -> Type) -> l -> Type) | p where
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
interface HSequence k l (p : (k -> Type) -> l -> Type) | p where
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
