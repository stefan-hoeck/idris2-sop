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

<code class="IdrisCode">
<span class="IdrisKeyword">module</span>&nbsp;<span class="IdrisModule">Docs.Intro</span><br />
<br />
<span class="IdrisKeyword">%default</span>&nbsp;<span class="IdrisKeyword">total</span><br />
</code>

## Product Types

Product types are data types with a single data constructor
such as records. For instance, here is a very basic definition
of an article in a web store:

<code class="IdrisCode">
<span class="IdrisKeyword">record</span>&nbsp;<span class="IdrisType">Article</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;constructor&nbsp;<span class="IdrisData">MkArticle</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">id</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Int</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">name</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">String</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">description</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">String</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">price</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Double</span><br />
</code>

We should be able to quickly write an `Eq` implementation for such a data type:

<code class="IdrisCode">
<span class="IdrisType">Eq</span>&nbsp;<span class="IdrisType">Article</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisData">MkArticle</span>&nbsp;<span class="IdrisBound">i1</span>&nbsp;<span class="IdrisBound">n1</span>&nbsp;<span class="IdrisBound">d1</span>&nbsp;<span class="IdrisBound">p1</span>&nbsp;<span class="IdrisFunction">==</span>&nbsp;<span class="IdrisData">MkArticle</span>&nbsp;<span class="IdrisBound">i2</span>&nbsp;<span class="IdrisBound">n2</span>&nbsp;<span class="IdrisBound">d2</span>&nbsp;<span class="IdrisBound">p2</span>&nbsp;<span class="IdrisKeyword">=</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisBound">i1</span>&nbsp;<span class="IdrisFunction">==</span>&nbsp;<span class="IdrisBound">i2</span>&nbsp;<span class="IdrisFunction">&amp;&amp;</span>&nbsp;<span class="IdrisBound">n1</span>&nbsp;<span class="IdrisFunction">==</span>&nbsp;<span class="IdrisBound">n2</span>&nbsp;<span class="IdrisFunction">&amp;&amp;</span>&nbsp;<span class="IdrisBound">d1</span>&nbsp;<span class="IdrisFunction">==</span>&nbsp;<span class="IdrisBound">d2</span>&nbsp;<span class="IdrisFunction">&amp;&amp;</span>&nbsp;<span class="IdrisBound">p1</span>&nbsp;<span class="IdrisFunction">==</span>&nbsp;<span class="IdrisBound">p2</span><br />
</code>

OK, that was rather boring, and - even worse - error-prone. Sure, Idris helps
us writing these kind of definitions by case splitting values for us,
but it usually can't find the desired implementation for us: The types
are not specific enough.

Let's write an implementation for `Ord`:

<code class="IdrisCode">
<span class="IdrisType">Ord</span>&nbsp;<span class="IdrisType">Article</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">compare</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">MkArticle</span>&nbsp;<span class="IdrisBound">i1</span>&nbsp;<span class="IdrisBound">n1</span>&nbsp;<span class="IdrisBound">d1</span>&nbsp;<span class="IdrisBound">p1</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">MkArticle</span>&nbsp;<span class="IdrisBound">i2</span>&nbsp;<span class="IdrisBound">n2</span>&nbsp;<span class="IdrisBound">d2</span>&nbsp;<span class="IdrisBound">p2</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">compare</span>&nbsp;<span class="IdrisBound">i1</span>&nbsp;<span class="IdrisBound">i2</span>&nbsp;<span class="IdrisFunction">&lt;+&gt;</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">compare</span>&nbsp;<span class="IdrisBound">n1</span>&nbsp;<span class="IdrisBound">n2</span>&nbsp;<span class="IdrisFunction">&lt;+&gt;</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">compare</span>&nbsp;<span class="IdrisBound">d1</span>&nbsp;<span class="IdrisBound">d2</span>&nbsp;<span class="IdrisFunction">&lt;+&gt;</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">compare</span>&nbsp;<span class="IdrisBound">p1</span>&nbsp;<span class="IdrisBound">p2</span><br />
</code>

Ugh. Considering that we sometimes have to define records with many more
fields, that's quite an amount of uninteresting code we have to write.

However, at least for `compare` there is a utility function `comparing`
allowing us to compare values through some other type with an
already existing `Ord` implementation.
Realizing that we can convert our record to a tuple and that tuples
of types with an `Ord` implementation have themselves an `Ord` implementation
leads us to the following code:

<code class="IdrisCode">
<span class="IdrisFunction">articleToTuple</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Article</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Int,String,String,Double</span><span class="IdrisKeyword">)</span><br />
<span class="IdrisFunction">articleToTuple</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">MkArticle</span>&nbsp;<span class="IdrisBound">i</span>&nbsp;<span class="IdrisBound">n</span>&nbsp;<span class="IdrisBound">d</span>&nbsp;<span class="IdrisBound">p</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">i</span><span class="IdrisData">,</span><span class="IdrisBound">n</span><span class="IdrisData">,</span><span class="IdrisBound">d</span><span class="IdrisData">,</span><span class="IdrisBound">p</span><span class="IdrisKeyword">)</span><br />
<br />
<span class="IdrisFunction">compareArticle</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Article</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Article</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Ordering</span><br />
<span class="IdrisFunction">compareArticle</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">comparing</span>&nbsp;<span class="IdrisFunction">articleToTuple</span><br />
</code>

That's better. Even more so, since we can use the same technique for
writing our `Eq` implementation:

<code class="IdrisCode">
<span class="IdrisFunction">eqVia</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Eq</span>&nbsp;<span class="IdrisBound">b</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">a</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisBound">b</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisBound">a</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisBound">a</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Bool</span><br />
<span class="IdrisFunction">eqVia</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">a1</span>&nbsp;<span class="IdrisBound">a2</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">a1</span>&nbsp;<span class="IdrisFunction">==</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">a2</span><br />
<br />
<span class="IdrisFunction">eqArticle</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Article</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Article</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Bool</span><br />
<span class="IdrisFunction">eqArticle</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">eqVia</span>&nbsp;<span class="IdrisFunction">articleToTuple</span><br />
</code>

We can also go in the other direction. Assume we have an interface
for decoding values from lists of strings (coming, for instance,
from a .csv file):

<code class="IdrisCode">
<span class="IdrisKeyword">interface</span>&nbsp;<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisBound">a</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Maybe</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">a</span><span class="IdrisType">,</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span><span class="IdrisKeyword">)</span><br />
<br />
<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisType">Int</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisData">Nil</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Nothing</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">h</span><span class="IdrisData">::</span><span class="IdrisBound">t</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Just</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">cast</span>&nbsp;<span class="IdrisBound">h</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisBound">t</span><span class="IdrisKeyword">)</span><br />
<br />
<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisData">Nil</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Nothing</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">h</span><span class="IdrisData">::</span><span class="IdrisBound">t</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Just</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">h</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisBound">t</span><span class="IdrisKeyword">)</span><br />
<br />
<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisType">Double</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisData">Nil</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Nothing</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">h</span><span class="IdrisData">::</span><span class="IdrisBound">t</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Just</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">cast</span>&nbsp;<span class="IdrisBound">h</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisBound">t</span><span class="IdrisKeyword">)</span><br />
<br />
<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisBound">a</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisBound">b</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">a</span><span class="IdrisType">,</span><span class="IdrisBound">b</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisBound">ss</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisKeyword">do</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">a</span><span class="IdrisData">,</span><span class="IdrisBound">ss&apos;</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;<span class="IdrisKeyword">&lt;-</span>&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisBound">ss</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">b</span><span class="IdrisData">,</span><span class="IdrisBound">ss&apos;&apos;</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">&lt;-</span>&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisBound">ss&apos;</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">pure</span>&nbsp;<span class="IdrisKeyword">((</span><span class="IdrisBound">a</span><span class="IdrisData">,</span><span class="IdrisBound">b</span><span class="IdrisKeyword">)</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisBound">ss&apos;&apos;</span><span class="IdrisKeyword">)</span><br />
</code>

We can again define a utility function for decoding product
types by using an intermediate representation with an
existing implementation of `Decode`:

<code class="IdrisCode">
<span class="IdrisFunction">decodeVia</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisBound">b</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">b</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisBound">a</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Maybe</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">a</span><span class="IdrisType">,</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span><span class="IdrisKeyword">)</span><br />
<span class="IdrisFunction">decodeVia</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">ss</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">map</span>&nbsp;<span class="IdrisKeyword">(\(</span><span class="IdrisBound">a</span><span class="IdrisData">,</span><span class="IdrisBound">ss</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">a</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisBound">ss</span><span class="IdrisKeyword">))</span>&nbsp;$&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisBound">ss</span><br />
</code>

Let's apply this to our own data type:

<code class="IdrisCode">
<span class="IdrisFunction">tupleToArticle</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Int,String,String,Double</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Article</span><br />
<span class="IdrisFunction">tupleToArticle</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">i</span><span class="IdrisData">,</span><span class="IdrisBound">n</span><span class="IdrisData">,</span><span class="IdrisBound">d</span><span class="IdrisData">,</span><span class="IdrisBound">p</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">MkArticle</span>&nbsp;<span class="IdrisBound">i</span>&nbsp;<span class="IdrisBound">n</span>&nbsp;<span class="IdrisBound">d</span>&nbsp;<span class="IdrisBound">p</span><br />
<br />
<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisType">Article</span>&nbsp;<span class="IdrisKeyword">where</span>&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">decodeVia</span>&nbsp;<span class="IdrisFunction">tupleToArticle</span><br />
<br />
<span class="IdrisFunction">decodeTest</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisData">Just</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">MkArticle</span>&nbsp;<span class="IdrisData">1</span>&nbsp;<span class="IdrisData">&quot;foo&quot;</span>&nbsp;<span class="IdrisData">&quot;bar&quot;</span>&nbsp;<span class="IdrisData">10.0,</span>&nbsp;<span class="IdrisData">Nil</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisData">[&quot;1&quot;,&quot;foo&quot;,&quot;bar&quot;,&quot;10.0&quot;]</span><br />
<span class="IdrisFunction">decodeTest</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
</code>

This approach of going via some isomorphic structure (that is, a structure
of the same shape) seems to be highly useful. The only boring
parts we still have to write are the minimalistic interface implementations
and the conversion functions from and to the utility data types.
This last part can be error-prone, especially when our product
types have many fields of the same type. Luckily, we can use
Idris to prove that we made no mistake:

<code class="IdrisCode">
<span class="IdrisFunction">toTupleId</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">x</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Article</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">tupleToArticle</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">articleToTuple</span>&nbsp;<span class="IdrisBound">x</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisBound">x</span><br />
<span class="IdrisFunction">toTupleId</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">MkArticle</span>&nbsp;<span class="IdrisKeyword">\_</span>&nbsp;<span class="IdrisKeyword">\_</span>&nbsp;<span class="IdrisKeyword">\_</span>&nbsp;<span class="IdrisKeyword">\_)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
<br />
<span class="IdrisFunction">fromTupleId</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">x</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Int,String,String,Double</span><span class="IdrisKeyword">))</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">articleToTuple</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">tupleToArticle</span>&nbsp;<span class="IdrisBound">x</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisBound">x</span><br />
<span class="IdrisFunction">fromTupleId</span>&nbsp;<span class="IdrisKeyword">(\_</span><span class="IdrisData">,</span><span class="IdrisKeyword">\_</span><span class="IdrisData">,</span><span class="IdrisKeyword">\_</span><span class="IdrisData">,</span><span class="IdrisKeyword">\_)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
</code>

## Sum Types

Now that we have articles for our web store, lets define some payment
methods we accept:

<code class="IdrisCode">
<span class="IdrisKeyword">data</span>&nbsp;<span class="IdrisType">Payment</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">CreditCard</span>&nbsp;<span class="IdrisType">String</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">|</span>&nbsp;<span class="IdrisData">Twint</span>&nbsp;<span class="IdrisType">String</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">|</span>&nbsp;<span class="IdrisData">Invoice</span><br />
</code>

Can we use the same techniques for implementing interfaces as
for product types? We can, if we choose the proper
representation. The canonical sum type is `Either`, so let's try this:

<code class="IdrisCode">
<span class="IdrisFunction">paymentToEither</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Payment</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Either</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Either</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisType">()</span><span class="IdrisKeyword">)</span><br />
<span class="IdrisFunction">paymentToEither</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">CreditCard</span>&nbsp;<span class="IdrisBound">s</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Left</span>&nbsp;<span class="IdrisBound">s</span><br />
<span class="IdrisFunction">paymentToEither</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Twint</span>&nbsp;<span class="IdrisBound">s</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Right</span>&nbsp;$&nbsp;<span class="IdrisData">Left</span>&nbsp;<span class="IdrisBound">s</span><br />
<span class="IdrisFunction">paymentToEither</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Invoice</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Right</span>&nbsp;$&nbsp;<span class="IdrisData">Right</span>&nbsp;<span class="IdrisData">()</span><br />
<br />
<span class="IdrisFunction">eitherToPayment</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Either</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Either</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisType">()</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Payment</span><br />
<span class="IdrisFunction">eitherToPayment</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Left</span>&nbsp;<span class="IdrisBound">s</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">CreditCard</span>&nbsp;<span class="IdrisBound">s</span><br />
<span class="IdrisFunction">eitherToPayment</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Right</span>&nbsp;$&nbsp;<span class="IdrisData">Left</span>&nbsp;<span class="IdrisBound">s</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Twint</span>&nbsp;<span class="IdrisBound">s</span><br />
<span class="IdrisFunction">eitherToPayment</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Right</span>&nbsp;$&nbsp;<span class="IdrisData">Right</span>&nbsp;<span class="IdrisData">()</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Invoice</span><br />
</code>

Here, it would be easy to mix up the similar payment methods `CreditCard`
and `Twint`, so we better verify that we made no mistake:

<code class="IdrisCode">
<span class="IdrisFunction">toEitherId</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">x</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Payment</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">eitherToPayment</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">paymentToEither</span>&nbsp;<span class="IdrisBound">x</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisBound">x</span><br />
<span class="IdrisFunction">toEitherId</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">CreditCard</span>&nbsp;<span class="IdrisBound">s</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
<span class="IdrisFunction">toEitherId</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Twint</span>&nbsp;<span class="IdrisBound">s</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
<span class="IdrisFunction">toEitherId</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Invoice</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
<br />
<span class="IdrisFunction">fromEitherId</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">x</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Either</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Either</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisType">()</span><span class="IdrisKeyword">))</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">paymentToEither</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">eitherToPayment</span>&nbsp;<span class="IdrisBound">x</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisBound">x</span><br />
<span class="IdrisFunction">fromEitherId</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Left</span>&nbsp;<span class="IdrisBound">s</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
<span class="IdrisFunction">fromEitherId</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Right</span>&nbsp;$&nbsp;<span class="IdrisData">Left</span>&nbsp;<span class="IdrisBound">s</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
<span class="IdrisFunction">fromEitherId</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Right</span>&nbsp;$&nbsp;<span class="IdrisData">Right</span>&nbsp;<span class="IdrisData">()</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
</code>

With that out of the way, we can reap the fruits of our labour
and implement `Eq` and `Ord`:

<code class="IdrisCode">
<span class="IdrisType">Eq</span>&nbsp;<span class="IdrisType">Payment</span>&nbsp;<span class="IdrisKeyword">where</span>&nbsp;<span class="IdrisFunction">(==)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">eqVia</span>&nbsp;<span class="IdrisFunction">paymentToEither</span><br />
<br />
<span class="IdrisType">Ord</span>&nbsp;<span class="IdrisType">Payment</span>&nbsp;<span class="IdrisKeyword">where</span>&nbsp;<span class="IdrisFunction">compare</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">comparing</span>&nbsp;<span class="IdrisFunction">paymentToEither</span><br />
</code>

## SOP : Sums of Products

The approach we take in this library is similar but more
versatile. Before we plunge into the full complexity of higher-kinded
sums of products, we use slightly simplified versions of
this library's core types in this section. We don't use
pairs but n-ary products (abbreviated `NP`) to represent
product types:

<code class="IdrisCode">
<span class="IdrisKeyword">data</span>&nbsp;<span class="IdrisType">NP</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">Type</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Type</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisData">Nil</span>&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">NP</span>&nbsp;<span class="IdrisData">[]</span><br />
&nbsp;&nbsp;<span class="IdrisData">(::)</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">v</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisBound">t</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">NP</span>&nbsp;<span class="IdrisBound">ts</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">NP</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">t</span>&nbsp;<span class="IdrisData">::</span>&nbsp;<span class="IdrisBound">ts</span><span class="IdrisKeyword">)</span><br />
</code>

Of course, this is nothing else than a
heterogeneous list.
Like with tuples, there is an isomorphism between a
product type and an n-ary product with the correct
size and value types. As an additional benefit, we
can specify the encoding of our data type as a list
of types. Let's do this for `Article`, write some
conversion functions and verify their correctness:

<code class="IdrisCode">
<span class="IdrisFunction">ArticleCode</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">ArticleCode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisType">Int</span><span class="IdrisData">,</span><span class="IdrisType">String</span><span class="IdrisData">,</span><span class="IdrisType">String</span><span class="IdrisData">,</span><span class="IdrisType">Double</span><span class="IdrisData">]</span><br />
<br />
<span class="IdrisFunction">articleToNp</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Article</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">NP</span>&nbsp;<span class="IdrisFunction">ArticleCode</span><br />
<span class="IdrisFunction">articleToNp</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">MkArticle</span>&nbsp;<span class="IdrisBound">i</span>&nbsp;<span class="IdrisBound">n</span>&nbsp;<span class="IdrisBound">d</span>&nbsp;<span class="IdrisBound">p</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisBound">i</span><span class="IdrisData">,</span><span class="IdrisBound">n</span><span class="IdrisData">,</span><span class="IdrisBound">d</span><span class="IdrisData">,</span><span class="IdrisBound">p</span><span class="IdrisData">]</span><br />
<br />
<span class="IdrisFunction">npToArticle</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">NP</span>&nbsp;<span class="IdrisFunction">ArticleCode</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Article</span><br />
<span class="IdrisFunction">npToArticle</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisBound">i</span><span class="IdrisData">,</span><span class="IdrisBound">n</span><span class="IdrisData">,</span><span class="IdrisBound">d</span><span class="IdrisData">,</span><span class="IdrisBound">p</span><span class="IdrisData">]</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">MkArticle</span>&nbsp;<span class="IdrisBound">i</span>&nbsp;<span class="IdrisBound">n</span>&nbsp;<span class="IdrisBound">d</span>&nbsp;<span class="IdrisBound">p</span><br />
<br />
<span class="IdrisFunction">toNpId</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">x</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Article</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">npToArticle</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">articleToNp</span>&nbsp;<span class="IdrisBound">x</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisBound">x</span><br />
<span class="IdrisFunction">toNpId</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">MkArticle</span>&nbsp;<span class="IdrisKeyword">\_</span>&nbsp;<span class="IdrisKeyword">\_</span>&nbsp;<span class="IdrisKeyword">\_</span>&nbsp;<span class="IdrisKeyword">\_)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
<br />
<span class="IdrisFunction">fromNpId</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">x</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">NP</span>&nbsp;<span class="IdrisFunction">ArticleCode</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">articleToNp</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">npToArticle</span>&nbsp;<span class="IdrisBound">x</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisBound">x</span><br />
<span class="IdrisFunction">fromNpId</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisKeyword">\_</span><span class="IdrisData">,</span><span class="IdrisKeyword">\_</span><span class="IdrisData">,</span><span class="IdrisKeyword">\_</span><span class="IdrisData">,</span><span class="IdrisKeyword">\_</span><span class="IdrisData">]</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
</code>

Likewise, we define n-ary sums for sum types:

<code class="IdrisCode">
<span class="IdrisKeyword">data</span>&nbsp;<span class="IdrisType">NS</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">Type</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Type</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisData">Z</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">v</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisBound">t</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">NS</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">t</span>&nbsp;<span class="IdrisData">::</span>&nbsp;<span class="IdrisBound">ts</span><span class="IdrisKeyword">)</span><br />
&nbsp;&nbsp;<span class="IdrisData">S</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">NS</span>&nbsp;<span class="IdrisBound">ts</span>&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">NS</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">t</span>&nbsp;<span class="IdrisData">::</span>&nbsp;<span class="IdrisBound">ts</span><span class="IdrisKeyword">)</span><br />
</code>

Let's look at how this affects our encoding for `Payment`:

<code class="IdrisCode">
<span class="IdrisFunction">PaymentCode</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">Type</span><br />
<span class="IdrisFunction">PaymentCode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisType">String</span><span class="IdrisData">,</span><span class="IdrisType">String</span><span class="IdrisData">,</span><span class="IdrisType">()</span><span class="IdrisData">]</span><br />
<br />
<span class="IdrisFunction">paymentToNs</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Payment</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">NS</span>&nbsp;<span class="IdrisFunction">PaymentCode</span><br />
<span class="IdrisFunction">paymentToNs</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">CreditCard</span>&nbsp;<span class="IdrisBound">s</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Z</span>&nbsp;<span class="IdrisBound">s</span><br />
<span class="IdrisFunction">paymentToNs</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Twint</span>&nbsp;<span class="IdrisBound">s</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">S</span>&nbsp;$&nbsp;<span class="IdrisData">Z</span>&nbsp;<span class="IdrisBound">s</span><br />
<span class="IdrisFunction">paymentToNs</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Invoice</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">S</span>&nbsp;$&nbsp;<span class="IdrisData">S</span>&nbsp;$&nbsp;<span class="IdrisData">Z</span>&nbsp;<span class="IdrisData">()</span><br />
<br />
<span class="IdrisFunction">nsToPayment</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">NS</span>&nbsp;<span class="IdrisFunction">PaymentCode</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Payment</span><br />
<span class="IdrisFunction">nsToPayment</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Z</span>&nbsp;<span class="IdrisBound">s</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">CreditCard</span>&nbsp;<span class="IdrisBound">s</span><br />
<span class="IdrisFunction">nsToPayment</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">S</span>&nbsp;$&nbsp;<span class="IdrisData">Z</span>&nbsp;<span class="IdrisBound">s</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Twint</span>&nbsp;<span class="IdrisBound">s</span><br />
<span class="IdrisFunction">nsToPayment</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">S</span>&nbsp;$&nbsp;<span class="IdrisData">S</span>&nbsp;$&nbsp;<span class="IdrisData">Z</span>&nbsp;<span class="IdrisData">()</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Invoice</span><br />
<br />
<span class="IdrisFunction">toNsId</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">x</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Payment</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">nsToPayment</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">paymentToNs</span>&nbsp;<span class="IdrisBound">x</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisBound">x</span><br />
<span class="IdrisFunction">toNsId</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">CreditCard</span>&nbsp;<span class="IdrisBound">s</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
<span class="IdrisFunction">toNsId</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Twint</span>&nbsp;<span class="IdrisBound">s</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
<span class="IdrisFunction">toNsId</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Invoice</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
<br />
<span class="IdrisFunction">fromNsId</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">x</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">NS</span>&nbsp;<span class="IdrisFunction">PaymentCode</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">paymentToNs</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">nsToPayment</span>&nbsp;<span class="IdrisBound">x</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisBound">x</span><br />
<span class="IdrisFunction">fromNsId</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">Z</span>&nbsp;<span class="IdrisBound">s</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
<span class="IdrisFunction">fromNsId</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">S</span>&nbsp;$&nbsp;<span class="IdrisData">Z</span>&nbsp;<span class="IdrisBound">s</span><span class="IdrisKeyword">)</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
<span class="IdrisFunction">fromNsId</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">S</span>&nbsp;$&nbsp;<span class="IdrisData">S</span>&nbsp;$&nbsp;<span class="IdrisData">Z</span>&nbsp;<span class="IdrisData">()</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
</code>

More general data types are sum types where each possible
choice is itself a product type: Sums of products. Indeed,
this is the most general structure a non-indexed Idris data type can
have (indexed data types can change their shape depending
on the index, which would lead to different generic representations,
again depending on the index). Below
is an example of such a data type, used to describe possible
user commands in a web store. I came up with this very
quickly, so it doesn't have to make too much sense:

<code class="IdrisCode">
<span class="IdrisKeyword">data</span>&nbsp;<span class="IdrisType">StoreCommand</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisData">Login</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">name</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">String</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">password</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">String</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">StoreCommand</span><br />
&nbsp;&nbsp;<span class="IdrisData">Logout</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">StoreCommand</span><br />
&nbsp;&nbsp;<span class="IdrisData">AddArticle</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">art</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Article</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">StoreCommand</span><br />
&nbsp;&nbsp;<span class="IdrisData">Checkout</span>&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">arts</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">Article</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">pay</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Payment</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">StoreCommand</span><br />
</code>

In order to encode this kind of sums of products, the *sop* library
provides data type `SOP`. We have to define this and
the remaining examples in this tutorial in their own namespace
to prevent constructor names from clashing with the ones
from `NS`:

<code class="IdrisCode">
<span class="IdrisKeyword">namespace</span>&nbsp;<span class="IdrisNamespace">SOP</span><br />
&nbsp;&nbsp;<span class="IdrisKeyword">data</span>&nbsp;<span class="IdrisType">SOP</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">tss</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;$&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">Type</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Type</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisData">Z</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">vs</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">NP</span>&nbsp;<span class="IdrisBound">ts</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">SOP</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">ts</span>&nbsp;<span class="IdrisData">::</span>&nbsp;<span class="IdrisBound">tss</span><span class="IdrisKeyword">)</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisData">S</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">SOP</span>&nbsp;<span class="IdrisBound">tss</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">SOP</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">ts</span>&nbsp;<span class="IdrisData">::</span>&nbsp;<span class="IdrisBound">tss</span><span class="IdrisKeyword">)</span><br />
</code>

We can use this data type to define a generic representation
for `StoreCommand`:

<code class="IdrisCode">
&nbsp;&nbsp;<span class="IdrisFunction">StoreCommandCode</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;$&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">Type</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">StoreCommandCode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">[[</span><span class="IdrisType">String</span><span class="IdrisData">,</span><span class="IdrisType">String</span><span class="IdrisData">],[],[</span><span class="IdrisType">Article</span><span class="IdrisData">],[</span><span class="IdrisType">List</span>&nbsp;<span class="IdrisType">Article</span><span class="IdrisData">,</span><span class="IdrisType">Payment</span><span class="IdrisData">]]</span><br />
</code>

It is an easy exercise left to the reader to implement
the following conversion functions and verify their correctness:

<code class="IdrisCode">
&nbsp;&nbsp;<span class="IdrisFunction">cmdToSop</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">StoreCommand</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">SOP</span>&nbsp;<span class="IdrisFunction">StoreCommandCode</span><br />
<br />
&nbsp;&nbsp;<span class="IdrisFunction">sopToCmd</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">SOP</span>&nbsp;<span class="IdrisFunction">StoreCommandCode</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">StoreCommand</span><br />
<br />
&nbsp;&nbsp;<span class="IdrisFunction">toSopId</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">x</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">StoreCommand</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">sopToCmd</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">cmdToSop</span>&nbsp;<span class="IdrisBound">x</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisBound">x</span><br />
<br />
&nbsp;&nbsp;<span class="IdrisFunction">fromSopId</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">x</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">SOP</span>&nbsp;<span class="IdrisFunction">StoreCommandCode</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">cmdToSop</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">sopToCmd</span>&nbsp;<span class="IdrisBound">x</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisBound">x</span><br />
</code>

## Generic : An interface for converting from and to generic representations

We are almost done with our introductory overview. This package
provides one more utility to complete the picture: Interface `Generic`.

<code class="IdrisCode">
&nbsp;&nbsp;<span class="IdrisKeyword">interface</span>&nbsp;<span class="IdrisType">Generic</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">t</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">code</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;$&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">Type</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">|</span>&nbsp;<span class="IdrisBound">t</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">from</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">v</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisBound">t</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">SOP</span>&nbsp;<span class="IdrisBound">code</span><br />
<br />
&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">to</span>&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">v</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">SOP</span>&nbsp;<span class="IdrisBound">code</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisBound">t</span><br />
<br />
&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">fromToId</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">v</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisBound">t</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisBound">to</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">from</span>&nbsp;<span class="IdrisBound">v</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisBound">v</span><br />
<br />
&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">toFromId</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">v</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">SOP</span>&nbsp;<span class="IdrisBound">code</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisBound">from</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">to</span>&nbsp;<span class="IdrisBound">v</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisBound">v</span><br />
</code>

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

