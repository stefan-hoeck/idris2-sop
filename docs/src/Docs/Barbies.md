# Barbies : Data Types that can change their Clothes

Before we continue with generic representations of data types,
I'd like to give a proper introduction to the higher-kinded version
of n-ary products. There is a Haskell library called
[barbies](https://github.com/jcpetruzza/barbies) providing similar
functionality for arbitrary higher-kinded data types. In theory,
the same functionality is provided by the *sop* library, through
the generic representation of data types.

## A Use Case for higher-kinded Products

Let's start with a first example, for which we will need a
proper module declaration and some imports.

```idris
module Docs.Barbies

import Data.SOP
import Data.Maybe

%default total
```

Consider a database application with some user data being stored
and a web interface for inspecting, modifying and deleting existing users
and adding new users. We could represent a user value in such
an application using the following record:

```idris
record User1 where
  constructor MkUser1
  id       : Int
  name     : String
  email    : String
  age      : Int
  password : String
```

While this is certainly a valid representation for a user data type,
it comes with several drawbacks. Could we, for instance, use the same
data type to create a new user from our web application? We could, but
the web application would have to provide a dummy value for the user's
ID, certainly a value the server application should be responsible
to generate. We'd also rather not send back the password to
people querying the database through the web application.

As these two examples show, our `User1` type should contain
different types of values for different use cases. We can achieve
this by using a parameterized data type:

```idris
record User2 idType pwType where
  constructor MkUser2
  id       : idType
  name     : String
  email    : String
  age      : Int
  password : pwType

User2Create : Type
User2Create = User2 () String

User2Web : Type
User2Web = User2 Int ()
```

This adds quite a bit of type-safety to our client-server application.
With properly typed request and response types, we will be forced to
remove the password from a user value before sending it to
the web client. We will also be forced to somehow come up with
and new ID, when the web client requests the creation of
a new user.

But what about updating existing users? We might want to design
our web client in such a way, that the values of certain fields
can be changed after double clicking the fields in question and
confirming our edits by pressing Enter. In such a setting it makes
sense that all fields are optional, with only the modified field
having a non-Nothing value. Such a thing cannot be represented by `User2`,
and we will have to use yet another, more flexible data type:

```idris
record User3 idType pwType (f : Type -> Type) where
  constructor MkUser3
  id       : f idType
  name     : f String
  email    : f String
  age      : f Int
  password : f pwType

User3DB : Type
User3DB = User3 Int String I

User3Create : Type
User3Create = User3 () String I

User3Web : Type
User3Web = User3 Int () I

User3Update : Type
User3Update = User3 () String Maybe

updateUser3 : User3Update -> User3DB -> User3DB
updateUser3 (MkUser3 _ mn me ma mp) (MkUser3 i n e a p) =
  MkUser3 i (fromMaybe n mn) (fromMaybe e me) (fromMaybe a ma) (fromMaybe p mp)
```

Great! We can specify, at the type level, exactly the amount of information
provided with each `User3` value. However, the implementation of
`updateUser3` is rather boiler-platy. Even more so, if we further
start to explore the possibilities these higher-kinded data types offer.

## Enter NP

All of the functionality above (and quite a bit more) is available
through data type `NP` from `Data.SOP`. Like `User3`, `NP` is
parameterized by a type-level function, allowing us to change
the context of the values wrapped in an n-ary product.

```idris
User4 : (idType : Type) -> (pwType : Type) -> (f : Type -> Type) -> Type
User4 idType pwType f = NP f [idType,String,String,Int,pwType]

User4DB : Type
User4DB = User4 Int String I

User4Create : Type
User4Create = User4 () String I

User4Web : Type
User4Web = User4 Int () I

User4Update : Type
User4Update = User4 () String Maybe
```

We can now use the combinators from `Data.NP` to write a more
concise form of `updateUser`:

```idris
update : forall a . Maybe a -> a -> a
update (Just a) _ = a
update Nothing  a = a

updateUser4 : User4Update -> User4DB -> User4DB
updateUser4 upd old =
  let upd' := setAt' () Int Nothing upd
   in hliftA2 update upd' old
```

Let's break this down a bit: Function `setAt` replaces the
first occurrence of the given type with a value of
a new type wrapped in the desired effect (`Maybe` in this case).
Since Idris cannot always infer the type of the new value
(as is the case here), function `setAt'` allows us to give
the type of the new value explicitly. So `upd'` now contains
values of the same type in the same order as `User4DB`
but all wrapped in a `Maybe`. We can therefore use function
`hliftA2` together with function `update` to actually
update the fields in user `old`.

Let's see how this works out.

```idris
export
testUpd : User4DB
testUpd =
  updateUser4
    [Nothing,Nothing,Nothing,Just 44,Nothing]
    [12,"hock","hock@me.ch",42,"top secret"]
```

We'll have to inspect the result at
the REPL (the compile time test I first wrote took
forever to typecheck):

```repl
Docs.Barbies> testUpd
[12, "hock", "hock@me.ch", 44, "top secret"]
```

## A Use Case for kind-polymorphic higher-kinded Products

"OK" you say, "but what about the nice record fields we
had before switching to that higher-kinded n-ary product thing?". There are
several possible answers. For instance, we could use a proper record
and go via the record's `Generic` instance to use
all that fancy higher-kinded stuff. We will look into that
possibility in another post. Or we could
make use of the fact that `NP` is polymorphic in the
kind of type-level tags it accepts. Let's look at that
option right now:

```idris
||| Presence or absence of an ID value
data IdField = IdYes | IdNo

||| Presence or absence of a password value
data PasswordField = PwYes | PwNo

||| Fields of a user data type
data UserField : Type where
  Id    : IdField -> UserField
  Name  : UserField
  EMail : UserField
  Age   : UserField
  PW    : PasswordField -> UserField

||| Converts a `UserField` to the corresponding
||| value type
FieldType : UserField -> Type
FieldType (Id IdYes) = Int
FieldType (Id IdNo)  = ()
FieldType Name       = String
FieldType EMail      = String
FieldType Age        = Int
FieldType (PW PwYes) = String
FieldType (PW PwNo)  = ()

||| There is no way to mix up field values. :-)
User : (i : IdField) -> (pw : PasswordField) -> (f : Type -> Type) -> Type
User i pw f = NP (f . FieldType) [Id i, Name, EMail, Age, PW pw]

UserDB : Type
UserDB = User IdYes PwYes I

UserWeb : Type
UserWeb = User IdYes PwNo I

UserCreate : Type
UserCreate = User IdNo PwYes I

UserUpdate : Type
UserUpdate = User IdNo PwYes Maybe

updateUser : UserUpdate -> UserDB -> UserDB
updateUser upd old =
  let upd' := setAt' (Id IdNo) (Id IdYes) Nothing upd
   in hliftA2 update upd' old
```

While the syntax is a bit more verbose that with proper
record fields, we gain a lot of flexibility with this
approach. In fact, by extending `NP` with some additional
functionality, it should be possible to turn it into
a quite versatile type of extensible records. Another post
for another day.

Using a special field type has quite a few advantages: First, we can
unambiguously specify the field we'd like to update or replace.
Second, we could also use fields together with a string conversion
function to implement a `Show` instance or JSON marshallers
for our `Person` type. We might look into these options
in another post.

## Comparison with Haskell's *sop-core*

When we compare the Idris implementation with Haskell's *sop-core*
library, both of them have their strong moments. Idris
allows us to much more naturally perform calculations
at the type level, while in Haskell the authors of *sop-core*
often had to go via `newtype` wrappers and `type family`
hoops to implement their functionality. On the other hand,
Haskell is much better at inferring types and kinds while
Idris often expects us to provide some additional type-level
hints to be satisfied with our code. Still, so far I like
the way Idris handles things a lot. The ability to
partially apply type-level functions as in the definition
of `User` is a really cool feature.

In addition, Idris allows us to use exactly the same data structures
for defining constraints, therefore, functions like `hcmap`
and `hcpure` can be implemented directly from `hliftA2`
and `hmap` respectively. This reduces the number of interfaces
we need.

## Conclusion

`NP_` and its relatives are highly versatile data types, the
usability of which we have only started to appreciate in this
post. In the [next post](Deriving.md), I'll have a look at automatically
deriving interface implementations using `Generic`.

<!-- vi: filetype=idris2:syntax=markdown
-->
