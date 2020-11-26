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

||| Constructor argument
public export
data ArgName : Type where
  NamedArg   : (index : Nat) -> (name : String) -> ArgName
  UnnamedArg : (index : Nat) -> ArgName

||| Name and arguments of a single data constructor
public export
data ConInfo : (ts : List Type) -> Type where
  MkConInfo : (name : NSName) -> (args : NP (K ArgName) ts) -> ConInfo ts

||| Name and constructors of a data type.
public export
data TypeInfo : (tss : List $ List Type) -> Type where
  MkTypeInfo : (name -> NSName) -> (cons : NP ConInfo tss) -> TypeInfo tss
