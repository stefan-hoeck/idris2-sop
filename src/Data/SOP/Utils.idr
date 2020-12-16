module Data.SOP.Utils

import Data.List
import Data.Strings

%default total

||| Type-level identity function.
public export
I : Type -> Type
I v = v

||| Type-level constant function.
public export
K : Type -> k -> Type
K t _ = t

--------------------------------------------------------------------------------
--          Interface Conversions
--------------------------------------------------------------------------------

||| Materializes an implicit value.
|||
||| This is useful for instance to convert a heterogeneous list of
||| `Ord` values to one of `Eq` values:
|||
||| ```idris example
||| ordToEqNP : NP (Ord . f) ks -> NP (Eq . f) ks
||| ordToEqNP = mapNP (\_ => materialize Eq)
||| ```
public export
materialize : (0 c : k -> Type) -> (instance : c v) => c v
materialize _ {instance} = instance

--------------------------------------------------------------------------------
--          Singleton Lists
--------------------------------------------------------------------------------

||| Witness that a list is actually a singleton list.
public export
data SingletonList : (vs : List a) -> Type where
  IsSingletonList : (v : a) -> SingletonList [v]

public export
Uninhabited (SingletonList []) where
  uninhabited v impossible

public export
Uninhabited (SingletonList $ a :: b :: t) where
  uninhabited v impossible

||| Covering function for singleton lists.
public export
singletonList : (vs : List a) -> Dec (SingletonList vs)
singletonList []              = No absurd
singletonList (v :: [])       = Yes (IsSingletonList v)
singletonList (_ :: (_ :: _)) = No absurd

--------------------------------------------------------------------------------
--          Updating Lists
--------------------------------------------------------------------------------

||| View for updating a single occurence of a value
||| in a list
public export
data UpdateOnce :  (t   : k)
                -> (t'  : k)
                -> (ks  : List k)
                -> (ks' : List k)
                -> Type where
  UpdateHere  : UpdateOnce t t' (t :: ks) (t' :: ks)
  UpdateThere : UpdateOnce t t' ks ks' -> UpdateOnce t t' (k :: ks) (k :: ks')

||| View for updating several occurences of a value
||| in a list
public export
data UpdateMany :  (t   : k)
                -> (t'  : k)
                -> (ks  : List k)
                -> (ks' : List k)
                -> Type where
  UMNil      : UpdateMany t t' [] []
  UMConsSame : UpdateMany t t' ks ks' -> UpdateMany t t' (t::ks) (t'::ks')
  UMConsDiff : UpdateMany t t' ks ks' -> UpdateMany t t' (k::ks) (k::ks')

--------------------------------------------------------------------------------
--          Sublists
--------------------------------------------------------------------------------

||| View of the second List containing all values (in the same order)
||| of the first List interleaved with arbitrary additional values.
public export
data Sublist : (ks : List k) -> (ks' : List k) -> Type where
  SLNil  : Sublist [] ks'
  SLSame : Sublist ks ks' -> Sublist (k::ks) (k::ks')
  SLDiff : Sublist ks ks' -> Sublist ks (k::ks')

--------------------------------------------------------------------------------
--          Show Utilities
--------------------------------------------------------------------------------

export
dispStringList : List String -> String
dispStringList ss = "[" ++ fastConcat (intersperse "," ss) ++ "]"
