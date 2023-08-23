# Introduction to Generic Representations of Data

The goal of his tutorial is to provide a quite thorough
introduction to the ideas
and benefits of *Generic Programming*: Abstracting over
the structure of data types by providing a few primitive
building blocks to describe this structure and then
derive functionality from these building blocks.

In this introduction, we start from the very beginning, so
no imports from the sop library are required.

This is a literate Idris source, hence:

```idris
module Docs.Intro

%default total
```

## Product Types

Product types are data types with a single data constructor
such as records. For instance, here is a very basic definition
of an article in a web store:

```idris
record Article where
  constructor MkArticle
  id          : Int
  name        : String
  description : String
  price       : Double
```

We should be able to quickly write an `Eq` implementation for such a data type:

```idris
Eq Article where
  MkArticle i1 n1 d1 p1 == MkArticle i2 n2 d2 p2 =
    i1 == i2 && n1 == n2 && d1 == d2 && p1 == p2
```

OK, that was rather boring, and - even worse - error-prone. Sure, Idris helps
us writing these kind of definitions by case splitting values for us,
but it usually can't find the desired implementation for us: The types
are not specific enough.

Let's write an implementation for `Ord`:

```idris
Ord Article where
  compare (MkArticle i1 n1 d1 p1) (MkArticle i2 n2 d2 p2) =
    compare i1 i2 <+>
    compare n1 n2 <+>
    compare d1 d2 <+>
    compare p1 p2
```

Ugh. Considering that we sometimes have to define records with many more
fields, that's quite an amount of uninteresting code we have to write.

However, at least for `compare` there is a utility function `comparing`
allowing us to compare values through some other type with an
already existing `Ord` implementation.
Realizing that we can convert our record to a tuple and that tuples
of types with an `Ord` implementation have themselves an `Ord` implementation
leads us to the following code:

```idris
articleToTuple : Article -> (Int,String,String,Double)
articleToTuple (MkArticle i n d p) = (i,n,d,p)

compareArticle : Article -> Article -> Ordering
compareArticle = comparing articleToTuple
```

That's better. Even more so, since we can use the same technique for
writing our `Eq` implementation:

```idris
eqVia : Eq b => (a -> b) -> a -> a -> Bool
eqVia f a1 a2 = f a1 == f a2

eqArticle : Article -> Article -> Bool
eqArticle = eqVia articleToTuple
```

We can also go in the other direction. Assume we have an interface
for decoding values from lists of strings (coming, for instance,
from a .csv file):

```idris
interface Decode a where
  decode : List String -> Maybe (a, List String)

Decode Int where
  decode Nil = Nothing
  decode (h::t) = Just (cast h, t)

Decode String where
  decode Nil = Nothing
  decode (h::t) = Just (h, t)

Decode Double where
  decode Nil = Nothing
  decode (h::t) = Just (cast h, t)

Decode a => Decode b => Decode (a,b) where
  decode ss = do
    (a,ss')  <- decode ss
    (b,ss'') <- decode ss'
    pure ((a,b), ss'')
```

We can again define a utility function for decoding product
types by using an intermediate representation with an
existing implementation of `Decode`:

```idris
decodeVia : Decode b => (b -> a) -> List String -> Maybe (a, List String)
decodeVia f ss = map (\(a,ss) => (f a, ss)) $ decode ss
```

Let's apply this to our own data type:

```idris
tupleToArticle : (Int,String,String,Double) -> Article
tupleToArticle (i,n,d,p) = MkArticle i n d p

Decode Article where decode = decodeVia tupleToArticle

decodeTest :
  Just (MkArticle 1 "foo" "bar" 10.0, Nil) =
  decode ["1","foo","bar","10.0"]
decodeTest = Refl
```

This approach of going via some isomorphic structure (that is, a structure
of the same shape) seems to be highly useful. The only boring
parts we still have to write are the minimalistic interface implementations
and the conversion functions from and to the utility data types.
This last part can be error-prone, especially when our product
types have many fields of the same type. Luckily, we can use
Idris to prove that we made no mistake:

```idris
toTupleId : (x : Article) -> tupleToArticle (articleToTuple x) = x
toTupleId (MkArticle _ _ _ _) = Refl

fromTupleId :
     (x : (Int,String,String,Double))
  -> articleToTuple (tupleToArticle x) = x
fromTupleId (_,_,_,_) = Refl
```

## Sum Types

Now that we have articles for our web store, lets define some payment
methods we accept:

```idris
data Payment : Type where
  CreditCard : String -> Payment
  Twint      : String -> Payment
  Invoice    : Payment
```

Can we use the same techniques for implementing interfaces as
for product types? We can, if we choose the proper
representation. The canonical sum type is `Either`, so let's try this:

```idris
paymentToEither : Payment -> Either String (Either String ())
paymentToEither (CreditCard s) = Left s
paymentToEither (Twint s)      = Right $ Left s
paymentToEither (Invoice)      = Right $ Right ()

eitherToPayment : Either String (Either String ()) -> Payment
eitherToPayment (Left s)           = CreditCard s
eitherToPayment (Right $ Left s)   = Twint s
eitherToPayment (Right $ Right ()) = Invoice
```

Here, it would be easy to mix up the similar payment methods `CreditCard`
and `Twint`, so we better verify that we made no mistake:

```idris
toEitherId : (x : Payment) -> eitherToPayment (paymentToEither x) = x
toEitherId (CreditCard s) = Refl
toEitherId (Twint s)      = Refl
toEitherId (Invoice)      = Refl

fromEitherId :
     (x : Either String (Either String ()))
  -> paymentToEither (eitherToPayment x) = x
fromEitherId (Left s)           = Refl
fromEitherId (Right $ Left s)   = Refl
fromEitherId (Right $ Right ()) = Refl
```

With that out of the way, we can reap the fruits of our labour
and implement `Eq` and `Ord`:

```idris
Eq Payment where (==) = eqVia paymentToEither

Ord Payment where compare = comparing paymentToEither
```

## SOP : Sums of Products

The approach we take in this library is similar but more
versatile. Before we plunge into the full complexity of higher-kinded
sums of products, we use slightly simplified versions of
this library's core types in this section. We don't use
pairs but n-ary products (abbreviated `NP`) to represent
product types:

```idris
data NP : List Type -> Type where
  Nil  : NP []
  (::) : (v : t) -> NP ts -> NP (t :: ts)
```

Of course, this is nothing else than a
heterogeneous list.
Like with tuples, there is an isomorphism between a
product type and an n-ary product with the correct
size and value types. As an additional benefit, we
can specify the encoding of our data type as a list
of types. Let's do this for `Article`, write some
conversion functions and verify their correctness:

```idris
ArticleCode : List Type
ArticleCode = [Int,String,String,Double]

articleToNp : Article -> NP ArticleCode
articleToNp (MkArticle i n d p) = [i,n,d,p]

npToArticle : NP ArticleCode -> Article
npToArticle [i,n,d,p] = MkArticle i n d p

toNpId : (x : Article) -> npToArticle (articleToNp x) = x
toNpId (MkArticle _ _ _ _) = Refl

fromNpId :  (x : NP ArticleCode) -> articleToNp (npToArticle x) = x
fromNpId [_,_,_,_] = Refl
```

Likewise, we define n-ary sums for sum types:

```idris
data NS : List Type -> Type where
  Z : (v : t) -> NS (t :: ts)
  S : NS ts   -> NS (t :: ts)
```

Let's look at how this affects our encoding for `Payment`:

```idris
PaymentCode : List Type
PaymentCode = [String,String,()]

paymentToNs : Payment -> NS PaymentCode
paymentToNs (CreditCard s) = Z s
paymentToNs (Twint s)      = S $ Z s
paymentToNs (Invoice)      = S $ S $ Z ()

nsToPayment : NS PaymentCode -> Payment
nsToPayment (Z s)          = CreditCard s
nsToPayment (S $ Z s)      = Twint s
nsToPayment (S $ S $ Z ()) = Invoice

toNsId :  (x : Payment) -> nsToPayment (paymentToNs x) = x
toNsId (CreditCard s) = Refl
toNsId (Twint s)      = Refl
toNsId (Invoice)      = Refl

fromNsId :  (x : NS PaymentCode) -> paymentToNs (nsToPayment x) = x
fromNsId (Z s)          = Refl
fromNsId (S $ Z s)      = Refl
fromNsId (S $ S $ Z ()) = Refl
```

More general data types are sum types where each possible
choice is itself a product type: Sums of products. Indeed,
this is the most general structure a non-indexed Idris data type can
have (indexed data types can change their shape depending
on the index, which would lead to different generic representations,
again depending on the index). Below
is an example of such a data type, used to describe possible
user commands in a web store. I came up with this very
quickly, so it doesn't have to make too much sense:

```idris
data StoreCommand : Type where
  Login      : (name : String) -> (password : String) -> StoreCommand
  Logout     : StoreCommand
  AddArticle : (art : Article) -> StoreCommand
  Checkout   : (arts : List Article) -> (pay : Payment) -> StoreCommand
```

In order to encode this kind of sums of products, the *sop* library
provides data type `SOP`. We have to define this and
the remaining examples in this tutorial in their own namespace
to prevent constructor names from clashing with the ones
from `NS`:

```idris
namespace SOP
  data SOP : (tss : List $ List Type) -> Type where
    Z : (vs : NP ts) -> SOP (ts :: tss)
    S : SOP tss -> SOP (ts :: tss)
```

We can use this data type to define a generic representation
for `StoreCommand`:

```idris
  StoreCommandCode : List $ List Type
  StoreCommandCode = [[String,String],[],[Article],[List Article,Payment]]
```

It is an easy exercise left to the reader to implement
the following conversion functions and verify their correctness:

```idris
  cmdToSop : StoreCommand -> SOP StoreCommandCode

  sopToCmd : SOP StoreCommandCode -> StoreCommand

  toSopId : (x : StoreCommand) -> sopToCmd (cmdToSop x) = x

  fromSopId : (x : SOP StoreCommandCode) -> cmdToSop (sopToCmd x) = x
```

## Generic : An interface for converting from and to generic representations

We are almost done with our introductory overview. This package
provides one more utility to complete the picture: Interface `Generic`.

```idris
  interface Generic (t : Type) (code : List $ List Type) | t where
    from : (v : t) -> SOP code

    to   : (v : SOP code) -> t

    fromToId : (v : t) -> to (from v) = v

    toFromId : (v : SOP code) -> from (to v) = v
```

It provides conversion functions for a data type from and to its
generic representation as a sum of product plus the
corresponding proofs that these functions actually represent
an isomorphism. Plus it comes with elaborator reflection utilities
to generate implementations of this interface automatically -
for a limited set of data types at least.

## What's next

This was quite a lengthy introduction. In the [next part](Barbies.md)
we will put the functionality of this library to use with some
example data types.

<!-- vi: filetype=idris2:syntax=markdown
-->
