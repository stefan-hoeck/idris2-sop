module Generics.Derive

import Data.List1
import public Generics.SOP
import public Generics.Meta
import public Decidable.Equality

import public Language.Reflection.Util

import System.Clock
import System.File

%language ElabReflection

%default total

--------------------------------------------------------------------------------
--          Generic
--------------------------------------------------------------------------------

private
ConNames : Type
ConNames = (Name, List Name, List TTImp)

||| Name of record `Generic`'s constructor.
export
mkGeneric : Name
mkGeneric = "MkGeneric"

-- Applies the proper n-ary sum constructor to a list
-- of arguments. `k` is the index of the data type's
-- constructor.
private
mkSOP' : (k : Nat) -> (arg : TTImp) -> TTImp
mkSOP' k arg = `(MkSOP ~(run k))

  where
    run : (n : Nat) -> TTImp
    run 0     = `(Z ~(arg))
    run (S n) = `(S ~(run n))

private
mkSOP : (k : Nat) -> (args : List TTImp) -> TTImp
mkSOP k args = mkSOP' k (listOf args)

||| Creates the syntax tree for the code of the given data type.
||| We export this since it might be useful elsewhere.
export
mkCode : (p : ParamTypeInfo) -> TTImp
mkCode p = listOf $ map (\c => listOf $ explicits c.args) p.cons

  where
    explicits : Vect n (ConArg p.numParams) -> List TTImp
    explicits [] = []
    explicits (CArg _ _ ExplicitArg t :: as) =
      ttimp p.paramNames t :: explicits as
    explicits (_ :: as) = explicits as

private
fromClause : (Nat,ConNames) -> Clause
fromClause (k,(con,ns,vars)) = patClause (bindAll con ns) (mkSOP k vars)

private
fromToIdClause : (Nat,ConNames) -> Clause
fromToIdClause (k,(con,ns,vars)) = patClause (bindAll con ns) `(Refl)

private
toClause : (Nat,ConNames) -> Clause
toClause (k,(con,ns,vars)) =
  patClause (mkSOP k $ map bindVar ns) (appAll con vars)

private
impossibleToClause : Nat -> Clause
impossibleToClause k = impossibleClause (mkSOP' k implicitTrue)

private
toFromIdClause : (Nat,ConNames) -> Clause
toFromIdClause (k,(con,ns,vars)) = patClause (mkSOP k $ map bindVar ns) `(Refl)

private
zipWithIndex : List a -> List (Nat,a)
zipWithIndex as = run 0 as

  where
    run : Nat -> List a -> List (Nat,a)
    run _ []     = []
    run k (h::t) = (k,h) :: run (S k) t

private
conNames : ParamCon n -> ConNames
conNames c =
  let ns   := toList $ freshNames "x" (count isExplicit c.args)
      vars := map var ns
   in (c.name, ns, vars)

||| Derives a `Generic` implementation for the given data type
||| and visibility.
export
GenericVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
GenericVis vis _ p =
  let names    := zipWithIndex (map conNames p.cons)
      fun      := UN . Basic $ "implGeneric" ++ camelCase p.info.name

      appType  := p.applied
      genType  := `(Generic ~(appType) ~(mkCode p))
      funType  := piAll genType p.implicits

      x        := lambdaArg {a = Name} "x"
      varX     := var "x"
      from     := lam x $ iCase varX implicitFalse (map fromClause names)
      to       := lam x $ iCase varX implicitFalse (map toClause names)
      fromToId := lam x $ iCase varX implicitFalse (map fromToIdClause names)
      toFromId := lam x $ iCase varX implicitFalse (map toFromIdClause names)

      impl     := appAll mkGeneric [from,to,fromToId,toFromId]

   in Right
       [ TL (interfaceHint vis fun funType) (def fun [patClause (var fun) impl])]

||| Alias for `GenericVis Public`.
export
Generic : List Name -> ParamTypeInfo -> Res (List TopLevel)
Generic = GenericVis Public

--------------------------------------------------------------------------------
--          Meta
--------------------------------------------------------------------------------

-- a string constant
private
str : String -> TTImp
str = primVal . Str

-- an int constant
private
int : Nat -> TTImp
int n = `(fromInteger ~(primVal $ BI (cast n)))

-- applies a name's namespace (List String) and name value
-- to a function (`con`) wrapped in a `TTImp`.
private
appNSName : Name -> (con,np : TTImp) -> TTImp
appNSName (NS (MkNS ss) (UN $ Basic s)) con np =
  let ss' := listOf $ reverse $ map str ss
   in `(~(con) ~(ss') ~(str s) ~(np))
appNSName n con np                          =
  let s := str $ nameStr n
   in `(~(con) [] ~(s) ~(np))

-- creates an ArgName's TTImp from an argument's index and name
private
argNameTTImp : (Nat,Maybe Name) -> TTImp
argNameTTImp (k, Just $ UN $ Basic n) = `(NamedArg ~(int k) ~(str n))
argNameTTImp (k, _)                   = `(UnnamedArg ~(int k))

-- creates a ConInfo's TTImp from a `ParamCon`.
private
conTTImp : ParamCon n -> TTImp
conTTImp c =
  let np := listOf $ map argNameTTImp (names 0 c.args)
   in appNSName c.name `(MkConInfo) np

  where
    names : (k : Nat) -> Vect m (ConArg n) -> List (Nat, Maybe Name)
    names k []                             = []
    names k (CArg n _ ExplicitArg t :: as) = (k,n) :: names (S k) as
    names k (_ :: as)                      = names k as

private
tiTTImp : ParamTypeInfo -> TTImp
tiTTImp p =
  let nps := map conTTImp p.cons
   in appNSName p.info.name `(MkTypeInfo) (listOf nps)

||| Derives a `Meta` implementation for the given data type
||| and visibility.
export
MetaVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
MetaVis vis _ p =
  let genType  := `(Meta ~(p.applied) ~(mkCode p))
      funType  := piAll genType p.implicits
      fun      := UN . Basic $ "implMeta" ++ camelCase p.info.name

      impl     := `(MkMeta ~(tiTTImp p))

   in Right
       [TL (interfaceHint vis fun funType) (def fun [patClause (var fun) impl])]

||| Alias for `EqVis Public`.
export
Meta : List Name -> ParamTypeInfo -> Res (List TopLevel)
Meta = MetaVis Public

--------------------------------------------------------------------------------
--          Eq
--------------------------------------------------------------------------------

||| Derives `Eq` for the given data type.
|||
||| @deprecated : This is deprecated. Use `Derive.Eq.Eq` from elab-util.
export %deprecate
Eq : List Name -> ParamTypeInfo -> Res (List TopLevel)
Eq _ p =
  let nm := implName p "Eq"
      cl := patClause (var nm) `(mkEq genEq)
   in Right [TL (interfaceHint Public nm (implType "Eq" p)) (def nm [cl])]

--------------------------------------------------------------------------------
--          Ord
--------------------------------------------------------------------------------

||| Derives `Ord` for the given data type.
|||
||| @deprecated : This is deprecated. Use `Derive.Ord.Ord` from elab-util.
export %deprecate
Ord : List Name -> ParamTypeInfo -> Res (List TopLevel)
Ord _ p =
  let nm := implName p "Ord"
      cl := patClause (var nm) `(mkOrd genCompare)
   in Right [TL (interfaceHint Public nm (implType "Ord" p)) (def nm [cl])]

--------------------------------------------------------------------------------
--          DecEq
--------------------------------------------------------------------------------

||| Derives `DecEq` for the given data type.
export
DecEq : List Name -> ParamTypeInfo -> Res (List TopLevel)
DecEq _ p =
  let nm := implName p "DecEq"
      cl := patClause (var nm) `(mkDecEq genDecEq)
   in Right [TL (interfaceHint Public nm (implType "DecEq" p)) (def nm [cl])]

--------------------------------------------------------------------------------
--          Show
--------------------------------------------------------------------------------

||| Derives `Show` for the given data type.
|||
||| @deprecated : This is deprecated. Use `Derive.Show.Show` from elab-util.
export %deprecate
Show : List Name -> ParamTypeInfo -> Res (List TopLevel)
Show _ p =
  let nm := implName p "Show"
      cl := patClause (var nm) `(mkShowPrec genShowPrec)
   in Right [TL (interfaceHint Public nm (implType "Show" p)) (def nm [cl])]

--------------------------------------------------------------------------------
--          Prelude and Data Implementations
--------------------------------------------------------------------------------

-- Prelude

%runElab derive "Nat" [Generic,Meta]

%runElab derive "Maybe" [Generic,Meta]


%runElab derive "Either" [Generic,Meta]

%runElab derive "List" [Generic,Meta]

%runElab derive "List1" [Generic,Meta]

%runElab derive "Dec" [Generic,Meta]

%runElab derive "Ordering" [Generic,Meta]

%runElab derive "Bool" [Generic,Meta]

%runElab derive "Prec" [Generic,Meta]

-- System

%runElab derive "System.File.Mode.Mode" [Generic,Meta]

%runElab derive "FileError" [Generic,Meta]

%runElab derive "File" [Generic,Meta]

%runElab derive "FileMode" [Generic,Meta]

%runElab derive "Permissions" [Generic,Meta]

%runElab derive "ClockType" [Generic,Meta]
