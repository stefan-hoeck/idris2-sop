||| Metadata about a data type's constructor and field names.
|||
||| Since for the time being, record syntax is still under discussion,
||| records are not yet treated any differently from other
||| product types. This might well change in the future, once
||| the issues about record syntax are resolved.
|||
||| Also, it seems not yet to be possible to get access to an
||| operator's fixity through elaborator reflection. We try to make
||| this information available as soon as possible.
module Generics.Meta

import Generics.SOP

%default total

||| Name and integer index of constructor arguments
public export
data ArgName : Type where

  ||| Name and index of a named argument
  NamedArg   : (index : Int) -> (name : String) -> ArgName

  ||| Index of an unnamed argument
  UnnamedArg : (index : Int) -> ArgName


||| Namespace, name and arguments of a single data constructor
|||
||| The arguments are wrapped in an n-ary product
||| parameterized by the constant functor, to make them
||| accessible to the SOP combinators.
public export
record ConInfo' (k : Type) (ks : List k) where
  constructor MkConInfo

  ||| Namespace of the constructor
  conNS   : List String

  ||| Name of the constructor
  conName : String

  ||| Constructor arguments
  args    : NP' k (K ArgName) ks

||| Alias for `ConInfo'` with the `k` parameter being implicit.
public export
ConInfo : {k : Type} -> (ks : List k) -> Type
ConInfo = ConInfo' k

||| Returns `True` if a constructor's `conName` consists
||| only of non-alphanumeric characters.
public export
isOperator : String -> Bool
isOperator = all (not . isAlphaNum) . unpack

||| Wraps a function name in parentheses if it is an operator
public export
wrapOperator : String -> String
wrapOperator n = if isOperator n then "(" ++ n ++ ")" else n

||| Namespace, name and constructors of a data type.
|||
||| The constructors are wrapped in an n-ary product
||| parameterized by `ConInfo`, to make them
||| accessible to the SOP combinators.
public export
record TypeInfo' (k : Type) (kss : List $ List k) where
  constructor MkTypeInfo

  ||| Namespace of the data type
  typeNS       : List String

  ||| Name of the data type
  typeName     : String

  ||| n-ary product of the data type's constructors
  constructors : NP' (List k) (ConInfo' k) kss

||| Alias for `TypeInfo'` with the `k` parameter being implicit.
public export
TypeInfo : {k : Type} -> (kss : List $ List k) -> Type
TypeInfo = TypeInfo' k

--------------------------------------------------------------------------------
--          Meta
--------------------------------------------------------------------------------

||| Interface to make a data type's metadata available at runtime.
|||
||| In order to get access to the meta data, it is often more convenient
||| to use function `metaFor`.
public export
interface Generic t code => Meta t code | t where
  meta : TypeInfo' Type code

||| Return's the `TypeInfo` of a data type. This is
||| an alias for `meta {t = t}`.
public export
metaFor : (0 t : Type) -> Meta t code => TypeInfo code
metaFor t = meta {t = t}

--------------------------------------------------------------------------------
--          Show Implementations
--------------------------------------------------------------------------------

-- Displays a single applied constructor wrapping it in parens if necessary
showC : NP (Show . f) ks => (p : Prec) -> ConInfo ks -> NP f ks -> String

-- No need to wrap a constant in parens
showC _ info []   = info.conName

-- This uses `showCon` from the Prelude to wrap an applied
-- constructor in parentheses depending on `p`.
showC p info args = let con    = wrapOperator info.conName
                        argStr = hconcat $ hcmap (Show . f) showArg args
                     in showCon p con argStr

showSOP :  (all : POP (Show . f) kss)
        => Prec -> TypeInfo kss -> SOP f kss -> String
showSOP {all = MkPOP _} p (MkTypeInfo _ _ cons) =
  hconcat . hcliftA2 (NP $ Show . f) (showC p) cons . unSOP

||| Generic show function.
|||
||| This is still quite basic. It uses prefix notation for operators
||| and treats records the same as other data types, that is,
||| record field names are not part of the generated string representation.
||| In addition, data types with List constructors (`Nil` and `(::)`)
||| are not yet displayed using list syntax ("[a,b,c]").
public export
genShowPrec : Meta t code => POP Show code => Prec -> t -> String
genShowPrec p = showSOP p (metaFor t) . from
