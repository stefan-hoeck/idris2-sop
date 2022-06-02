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
of data types has been added recently,
together with the ability to automatically derive implementations for `Show`.

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

%runElab derive "Employee" [Generic, Meta, Eq, Ord, Show]
```

Note: If a data type includes lazy fields, module `Data.Lazy`
should be imported as well when deriving interface implementations.
## Documentation

Most of the exported functions have been properly annotated
with doc strings. In addition, there is an extensive - and still growing -
[tutorial](src/Doc/Index.md) about the core ideas and techniques
behind the SOP approach to generic programming.

## Prerequisites

In order to automatically derive interface implementations,
this library makes use of functionality provided by the
[idris2-elab-util](https://github.com/stefan-hoeck/idris2-elab-util) package.

### Idris2 Version

Starting from Idris2 version 0.5.1, tagged releases of the same
minor version number (e.g. 0.5.x) will be made available, while the main
branch keeps following the Idris2 main branch.

The latest commit is daily tested to build against the current
HEAD of the Idris compiler. Since Idris2 releases are happening
rather infrequently at the moment, it is suggested to use
a package manager like [pack](https://github.com/stefan-hoeck/idris2-pack)
to install and maintain matching versions of the Idris compiler
and this library. Pack will also automatically install all
required dependencies.

## Limitations

Below is a non-comprehensive list of limitations and caveats of this library.

### Totality

The totality checker does not consider derived interface implementations
for inductive types to be total, since from the conversion to
the generic representation it seems not to be able to figure out
that the values to be processed are actually getting any smaller.

### Performance

This library has not yet been optimized in terms of performance.
For instance, there have so far been no investigations into
the amount of laziness we should support when converting values
from and to their generic representations. In contrast do the
Haskell version, `NP` and `NS` are both strict heterogeneous
containers.

Also, generic `Eq` and `Ord` implementations might carry out more
comparisons than strictly necessary in cases where the
result can be decided early on.
