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
