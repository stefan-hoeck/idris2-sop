# Sums of Products: A Tutorial about Generics and Barbies

This is a port of Haskell's [generics-sop](https://github.com/well-typed/generics-sop)
library, where data types are represented as n-ary sums over n-ary products.
Such a generic representation is useful for two reasons: First, and most important,
it allows us to automatically derive interface implementations with a
minimal amount of code for a large set of data types. Second, the combinators
provided by this library present a powerful toolkit
for manipulating data types when in their generic form.

In this tutorial, we address both aspects of generic programming
in the SOP style, while showing at the same time, how a minimal
amount of reflection code can be used to fully automatize the deriving
of several interface implementations all at once
using elaborator reflection.

## Table of Contents

1. [Introduction to Generic Representations of Data](Intro.md)
2. [Barbies : Data Types that can change their Clothes](Barbies.md)
3. [Deriving Interface Implementations](Deriving.md)
4. [Metadata](Metadata.md)
