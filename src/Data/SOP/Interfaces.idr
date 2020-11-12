module Data.SOP.Interfaces

import Data.SOP.Utils

%default total

public export
interface HPure (h : forall k . (k -> Type) -> List k -> Type) where
  hpure : {ks : List k} -> (forall k . f k) -> h f ks

  cpure : {ks : List k}
        -> (c : k -> Type)
        -> All c ks
        => (forall k . c k => f k)
        -> h f ks

public export
interface HAp (h : forall k . (k -> Type) -> List k -> Type) where
  hap : {0 ks : List k} -> (forall k . f k -> g k) -> h f ks -> h g ks
