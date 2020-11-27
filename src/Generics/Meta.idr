||| Metadata about constructor and field names.
module Generics.Meta

import Generics.SOP

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
  NamedArg   : (index : Int) -> (name : String) -> ArgName
  UnnamedArg : (index : Int) -> ArgName

||| Name and arguments of a single data constructor
public export
record ConInfo (k : Type) (ks : List k) where
  constructor MkConInfo
  conName : NSName
  args    : NP' k (K ArgName) ks

||| Name and constructors of a data type.
public export
record TypeInfo (k : Type) (kss : List $ List k) where
  constructor MkTypeInfo
  typeName     : NSName
  constructors : NP' (List k) (ConInfo k) kss

--------------------------------------------------------------------------------
--          Meta
--------------------------------------------------------------------------------

public export
interface Generic t code => Meta t code | t where
  meta : TypeInfo Type code

public export
metaFor : (0 t : Type) -> Meta t code => TypeInfo Type code
metaFor t = meta {t = t}

--------------------------------------------------------------------------------
--          Show Implementations
--------------------------------------------------------------------------------

showCon : NP (Show . f) ks => (p : Prec) -> ConInfo k ks -> NP f ks -> String
showCon p info args = showCon p con argStr
  where con : String
        con = let con = info.conName.con
               in if isOperator info.conName then "(" ++ con ++ ")" else con

        argStr : String
        argStr = hconcat $ hcmap (Show . f) showArg args

showValue :  (all : POP (Show . f) kss)
          => Prec -> TypeInfo k kss -> SOP f kss -> String
showValue {all = MkPOP _} p (MkTypeInfo _ cons) =
  hconcat . hcliftA2 (NP $ Show . f) (showCon p) cons . unSOP


public export
genShow : Meta t code => POP Show code => Prec -> t -> String
genShow p v = showValue p (metaFor t) (from v)
