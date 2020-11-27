||| Metadata about constructor and field names.
module Generics.Meta

import Data.SOP

%default total

||| Represents a data constructor's or data type's
||| fully qualified name.
public export
record NSName where
  constructor MkNSName
  ns  : List String
  con : String

public export
isOperator : NSName -> Bool
isOperator = all (not . isAlphaNum) . unpack . con

||| Constructor argument
public export
data ArgName : Type where
  NamedArg   : (index : Nat) -> (name : String) -> ArgName
  UnnamedArg : (index : Nat) -> ArgName

||| Name and arguments of a single data constructor
public export
record ConInfo (ts : List Type) where
  constructor MkConInfo
  conName : NSName
  args    : NP (K ArgName) ts

||| Name and constructors of a data type.
public export
record TypeInfo (tss : List $ List Type) where
  constructor MkTypeInfo
  typeName     : NSName
  constructors : NP ConInfo tss

--------------------------------------------------------------------------------
--          Show Implementations
--------------------------------------------------------------------------------

showConstructor : NP (Show . f) ts => ConInfo ts -> Prec -> NP f ts -> String
showConstructor info p args = showCon p conName argStr
  where conName : String
        conName = let con = info.conName.con
                   in if isOperator info.conName then "(" ++ con ++ ")" else con

        argStr : String
        argStr = hconcat $ hcmap (Show . f) showArg args

showValue : POP (Show . f) tss => TypeInfo tss -> Prec -> SOP f tss -> String
