<style>
.IdrisData {
  color: darkred
}
.IdrisType {
  color: blue
}
.IdrisBound {
  color: black
}
.IdrisFunction {
  color: darkgreen
}
.IdrisKeyword {
  text-decoration: underline;
}
.IdrisComment {
  color: #b22222
}
.IdrisNamespace {
  font-style: italic;
  color: black
}
.IdrisPostulate {
  font-weight: bold;
  color: red
}
.IdrisModule {
  font-style: italic;
  color: black
}
.IdrisCode {
  display: block;
  background-color: whitesmoke;
}
</style>
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

<code class="IdrisCode">
<span class="IdrisKeyword">module</span>&nbsp;<span class="IdrisModule">Docs.Barbies</span><br />
<br />
<span class="IdrisKeyword">import</span>&nbsp;<span class="IdrisModule">Data.SOP</span><br />
<span class="IdrisKeyword">import</span>&nbsp;<span class="IdrisModule">Data.Maybe</span><br />
<br />
<span class="IdrisKeyword">%default</span>&nbsp;<span class="IdrisKeyword">total</span><br />
</code>

Consider a database application with some user data being stored
and a web interface for inspecting, modifying and deleting existing users
and adding new users. We could represent a user value in such
an application using the following record:

<code class="IdrisCode">
<span class="IdrisKeyword">record</span>&nbsp;<span class="IdrisType">User1</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;constructor&nbsp;<span class="IdrisData">MkUser1</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">id</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Int</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">name</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">String</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">email</span>&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">String</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">age</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Int</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">password</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">String</span><br />
</code>

While this is certainly a valid representation for a user data type,
it comes with several drawbacks. Could we, for instance, use the same
data type to create a new user from our web application? We could, but
the web application would have to provide a dummy value for the user's
id, certainly a value the server application should be responsible
to generate. We'd also rather not send back the password to
people querying the database through the web application.

As these two examples show, our `User1` type should contain
different types of values for different use cases. We can achieve
this by using a parameterized data type:

<code class="IdrisCode">
<span class="IdrisKeyword">record</span>&nbsp;<span class="IdrisType">User2</span>&nbsp;<span class="IdrisBound">idType</span>&nbsp;<span class="IdrisBound">pwType</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;constructor&nbsp;<span class="IdrisData">MkUser2</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">id</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisBound">idType</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">name</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">String</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">email</span>&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">String</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">age</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Int</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">password</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisBound">pwType</span><br />
<br />
<span class="IdrisFunction">User2Create</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">User2Create</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisType">User2</span>&nbsp;<span class="IdrisType">()</span>&nbsp;<span class="IdrisType">String</span><br />
<br />
<span class="IdrisFunction">User2Web</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">User2Web</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisType">User2</span>&nbsp;<span class="IdrisType">Int</span>&nbsp;<span class="IdrisType">()</span><br />
</code>

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

<code class="IdrisCode">
<span class="IdrisKeyword">record</span>&nbsp;<span class="IdrisType">User3</span>&nbsp;<span class="IdrisBound">idType</span>&nbsp;<span class="IdrisBound">pwType</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">f</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Type</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;constructor&nbsp;<span class="IdrisData">MkUser3</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">id</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">idType</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">name</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisType">String</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">email</span>&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisType">String</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">age</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisType">Int</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">password</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">pwType</span><br />
<br />
<span class="IdrisFunction">User3DB</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">User3DB</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisType">User3</span>&nbsp;<span class="IdrisType">Int</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisFunction">I</span><br />
<br />
<span class="IdrisFunction">User3Create</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">User3Create</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisType">User3</span>&nbsp;<span class="IdrisType">()</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisFunction">I</span><br />
<br />
<span class="IdrisFunction">User3Web</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">User3Web</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisType">User3</span>&nbsp;<span class="IdrisType">Int</span>&nbsp;<span class="IdrisType">()</span>&nbsp;<span class="IdrisFunction">I</span><br />
<br />
<span class="IdrisFunction">User3Update</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">User3Update</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisType">User3</span>&nbsp;<span class="IdrisType">()</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisType">Maybe</span><br />
<br />
<span class="IdrisFunction">updateUser3</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisFunction">User3Update</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">User3DB</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">User3DB</span><br />
<span class="IdrisFunction">updateUser3</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">MkUser3</span>&nbsp;<span class="IdrisKeyword">\_</span>&nbsp;<span class="IdrisBound">mn</span>&nbsp;<span class="IdrisBound">me</span>&nbsp;<span class="IdrisBound">ma</span>&nbsp;<span class="IdrisBound">mp</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">MkUser3</span>&nbsp;<span class="IdrisBound">i</span>&nbsp;<span class="IdrisBound">n</span>&nbsp;<span class="IdrisBound">e</span>&nbsp;<span class="IdrisBound">a</span>&nbsp;<span class="IdrisBound">p</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span><br />
&nbsp;&nbsp;<span class="IdrisData">MkUser3</span>&nbsp;<span class="IdrisBound">i</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">fromMaybe</span>&nbsp;<span class="IdrisBound">n</span>&nbsp;<span class="IdrisBound">mn</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">fromMaybe</span>&nbsp;<span class="IdrisBound">e</span>&nbsp;<span class="IdrisBound">me</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">fromMaybe</span>&nbsp;<span class="IdrisBound">a</span>&nbsp;<span class="IdrisBound">ma</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">fromMaybe</span>&nbsp;<span class="IdrisBound">p</span>&nbsp;<span class="IdrisBound">mp</span><span class="IdrisKeyword">)</span><br />
</code>

Great! We can specify, at the type level, exactly the amount of information
provided with each `User3` value. However, the implementation of
`updateUser3` is rather boiler-platy. Even more so, if we further
start to explore the possibilities these higher-kinded data types offer.

## Enter NP

All of the functionality above (and quite a bit more) is available
through data type `NP` from `Data.SOP`. Like `User3`, `NP` is
parameterized by a type-level function, allowing us to change
the context of the values wrapped in an n-ary product.

<code class="IdrisCode">
<span class="IdrisFunction">User4</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">idType</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">pwType</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">f</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Type</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">User4</span>&nbsp;<span class="IdrisBound">idType</span>&nbsp;<span class="IdrisBound">pwType</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">NP</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisBound">idType</span><span class="IdrisData">,</span><span class="IdrisType">String</span><span class="IdrisData">,</span><span class="IdrisType">String</span><span class="IdrisData">,</span><span class="IdrisType">Int</span><span class="IdrisData">,</span><span class="IdrisBound">pwType</span><span class="IdrisData">]</span><br />
<br />
<span class="IdrisFunction">User4DB</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">User4DB</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">User4</span>&nbsp;<span class="IdrisType">Int</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisFunction">I</span><br />
<br />
<span class="IdrisFunction">User4Create</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">User4Create</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">User4</span>&nbsp;<span class="IdrisType">()</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisFunction">I</span><br />
<br />
<span class="IdrisFunction">User4Web</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">User4Web</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">User4</span>&nbsp;<span class="IdrisType">Int</span>&nbsp;<span class="IdrisType">()</span>&nbsp;<span class="IdrisFunction">I</span><br />
<br />
<span class="IdrisFunction">User4Update</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">User4Update</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">User4</span>&nbsp;<span class="IdrisType">()</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisType">Maybe</span><br />
</code>

We can now use the combinators from `Data.NP` to write a more
concise form of `updateUser`:

<code class="IdrisCode">
<span class="IdrisFunction">update</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">forall</span>&nbsp;<span class="IdrisBound">a</span>&nbsp;<span class="IdrisKeyword">.</span>&nbsp;<span class="IdrisType">Maybe</span>&nbsp;<span class="IdrisBound">a</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisBound">a</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisBound">a</span><br />
<span class="IdrisFunction">update</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Just</span>&nbsp;<span class="IdrisBound">a</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">\_</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisBound">a</span><br />
<span class="IdrisFunction">update</span>&nbsp;<span class="IdrisData">Nothing</span>&nbsp;&nbsp;<span class="IdrisBound">a</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisBound">a</span><br />
<br />
<span class="IdrisFunction">updateUser4</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisFunction">User4Update</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">User4DB</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">User4DB</span><br />
<span class="IdrisFunction">updateUser4</span>&nbsp;<span class="IdrisBound">upd</span>&nbsp;<span class="IdrisBound">old</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisKeyword">let</span>&nbsp;<span class="IdrisBound">upd&apos;</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">setAt&apos;</span>&nbsp;<span class="IdrisType">()</span>&nbsp;<span class="IdrisType">Int</span>&nbsp;<span class="IdrisData">Nothing</span>&nbsp;<span class="IdrisBound">upd</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">in</span>&nbsp;<span class="IdrisFunction">hliftA2</span>&nbsp;<span class="IdrisFunction">update</span>&nbsp;<span class="IdrisBound">upd&apos;</span>&nbsp;<span class="IdrisBound">old</span><br />
</code>

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

<code class="IdrisCode">
<span class="IdrisKeyword">export</span><br />
<span class="IdrisFunction">testUpd</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisFunction">User4DB</span><br />
<span class="IdrisFunction">testUpd</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">updateUser4</span>&nbsp;<span class="IdrisData">[Nothing,Nothing,Nothing,Just</span>&nbsp;<span class="IdrisData">44,Nothing]</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisData">[12,&quot;hock&quot;,&quot;hock@me.ch&quot;,42,&quot;top&nbsp;secret&quot;]</span><br />
</code>

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

<code class="IdrisCode">
<span class="IdrisComment">|||&nbsp;Presence&nbsp;or&nbsp;absence&nbsp;of&nbsp;an&nbsp;ID&nbsp;value</span><br />
<span class="IdrisKeyword">data</span>&nbsp;<span class="IdrisType">IdField</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">IdYes</span>&nbsp;<span class="IdrisKeyword">|</span>&nbsp;<span class="IdrisData">IdNo</span><br />
<br />
<span class="IdrisComment">|||&nbsp;Presence&nbsp;or&nbsp;absence&nbsp;of&nbsp;a&nbsp;password&nbsp;value</span><br />
<span class="IdrisKeyword">data</span>&nbsp;<span class="IdrisType">PasswordField</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">PwYes</span>&nbsp;<span class="IdrisKeyword">|</span>&nbsp;<span class="IdrisData">PwNo</span><br />
<br />
<span class="IdrisComment">|||&nbsp;Fields&nbsp;of&nbsp;a&nbsp;user&nbsp;data&nbsp;type</span><br />
<span class="IdrisKeyword">data</span>&nbsp;<span class="IdrisType">UserField</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Id</span>&nbsp;<span class="IdrisType">IdField</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">|</span>&nbsp;<span class="IdrisData">Name</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">|</span>&nbsp;<span class="IdrisData">EMail</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">|</span>&nbsp;<span class="IdrisData">Age</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">|</span>&nbsp;<span class="IdrisData">PW</span>&nbsp;<span class="IdrisType">PasswordField</span><br />
<br />
<span class="IdrisComment">|||&nbsp;Converts&nbsp;a&nbsp;`UserField`&nbsp;to&nbsp;the&nbsp;corresponding</span><br />
<span class="IdrisComment">|||&nbsp;value&nbsp;type</span><br />
<span class="IdrisFunction">FieldType</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">UserField</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">FieldType</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Id</span>&nbsp;<span class="IdrisData">IdYes</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisType">Int</span><br />
<span class="IdrisFunction">FieldType</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Id</span>&nbsp;<span class="IdrisData">IdNo</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisType">()</span><br />
<span class="IdrisFunction">FieldType</span>&nbsp;<span class="IdrisData">Name</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisType">String</span><br />
<span class="IdrisFunction">FieldType</span>&nbsp;<span class="IdrisData">EMail</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisType">String</span><br />
<span class="IdrisFunction">FieldType</span>&nbsp;<span class="IdrisData">Age</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisType">Int</span><br />
<span class="IdrisFunction">FieldType</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">PW</span>&nbsp;<span class="IdrisData">PwYes</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisType">String</span><br />
<span class="IdrisFunction">FieldType</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">PW</span>&nbsp;<span class="IdrisData">PwNo</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisType">()</span><br />
<br />
<span class="IdrisComment">|||&nbsp;There&nbsp;is&nbsp;no&nbsp;way&nbsp;to&nbsp;mix&nbsp;up&nbsp;field&nbsp;values.&nbsp;:-)</span><br />
<span class="IdrisFunction">User</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">i</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">IdField</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">pw</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">PasswordField</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">f</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Type</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">User</span>&nbsp;<span class="IdrisBound">i</span>&nbsp;<span class="IdrisBound">pw</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">NP</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">f</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisFunction">FieldType</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisData">[Id</span>&nbsp;<span class="IdrisBound">i</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisData">Name,</span>&nbsp;<span class="IdrisData">EMail,</span>&nbsp;<span class="IdrisData">Age,</span>&nbsp;<span class="IdrisData">PW</span>&nbsp;<span class="IdrisBound">pw</span><span class="IdrisData">]</span><br />
<br />
<span class="IdrisFunction">UserDB</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">UserDB</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">User</span>&nbsp;<span class="IdrisData">IdYes</span>&nbsp;<span class="IdrisData">PwYes</span>&nbsp;<span class="IdrisFunction">I</span><br />
<br />
<span class="IdrisFunction">UserWeb</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">UserWeb</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">User</span>&nbsp;<span class="IdrisData">IdYes</span>&nbsp;<span class="IdrisData">PwNo</span>&nbsp;<span class="IdrisFunction">I</span><br />
<br />
<span class="IdrisFunction">UserCreate</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">UserCreate</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">User</span>&nbsp;<span class="IdrisData">IdNo</span>&nbsp;<span class="IdrisData">PwYes</span>&nbsp;<span class="IdrisFunction">I</span><br />
<br />
<span class="IdrisFunction">UserUpdate</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">UserUpdate</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">User</span>&nbsp;<span class="IdrisData">IdNo</span>&nbsp;<span class="IdrisData">PwYes</span>&nbsp;<span class="IdrisType">Maybe</span><br />
<br />
<span class="IdrisFunction">updateUser</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisFunction">UserUpdate</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">UserDB</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">UserDB</span><br />
<span class="IdrisFunction">updateUser</span>&nbsp;<span class="IdrisBound">upd</span>&nbsp;<span class="IdrisBound">old</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisKeyword">let</span>&nbsp;<span class="IdrisBound">upd&apos;</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">setAt&apos;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Id</span>&nbsp;<span class="IdrisData">IdNo</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Id</span>&nbsp;<span class="IdrisData">IdYes</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisData">Nothing</span>&nbsp;<span class="IdrisBound">upd</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">in</span>&nbsp;<span class="IdrisFunction">hliftA2</span>&nbsp;<span class="IdrisFunction">update</span>&nbsp;<span class="IdrisBound">upd&apos;</span>&nbsp;<span class="IdrisBound">old</span><br />
</code>

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

