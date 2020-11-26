# idris2-sop : Sums of Products


This is a library about generic representations of algebraic data types
as n-ary sums over n-ary products
inspired by Haskell's [sop-core](https://hackage.haskell.org/package/sop-core)
and [generic-sop](https://hackage.haskell.org/package/generics-sop) libraries.

While still very much work in progress, many combinators from *sop-core*
are implemented and ready to be used. Implementations for `Generic`,
an interface for converting data types from and to their
generic representations as sums of products, can be derived automatically
using elaborator reflection. In addition, implementations for
`Eq`, `Ord`, `DecEq`, `Semigroup`, and `Monoid` can also be
derived automatically by going via a data type's generic representation.

Support for providing access to metadata like constructor and argument names
of data types
will follow shortly, together with the ability to automatically derive
implementations for `Show`.

## Motivating Example

With just a single import and after enabling `%language ElabReflection`,
interface implementations can be derived as follows:

```idris
module README

import Generics.Derive

%language ElabReflection

record Employee where
  constructor MkEmployee
  name       : String
  age        : Nat
  salary     : Double
  supervisor : Maybe Employee

%runElab derive "Employee" [Generic, Eq, Ord]
```

## Documentation

Most of the exported functions have been properly annotated
with doc strings. In addition, there is a - still growing - 
[tutorial](src/Doc/Index.md) about the core ideas and techniques
behind the SOP approach to generic programming.

## Prerequisites

In order to automatically derive interface implementations,
this library makes use of functionality provided by the
[idris2-elab-util](https://github.com/stefan-hoeck/idris2-elab-util) package.
