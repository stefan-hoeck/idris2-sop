module Data.SOP.Utils

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

||| Generation function for singleton lists.
public export
singletonList : (vs : List a) -> Dec (SingletonList vs)
singletonList []              = No absurd
singletonList (v :: [])       = Yes (IsSingletonList v)
singletonList (_ :: (_ :: _)) = No absurd
