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
# Deriving Interface Implementations

A lot of ink has already been spilled over how we can use
generic representations to automatically derive interface
implementations, and I wrote several lengthy posts
about this topic for the
[idris2-elab-util](https://github.com/stefan-hoeck/idris2-elab-util)
package. Therefore, in this post, I'll only give examples about
how this library can be used to derive interface implementations
for a large group of data types automatically, without
going into the details about the underlying metaprogramming
machinery.

We start with the necessary imports and language extensions:

<code class="IdrisCode">
<span class="IdrisKeyword">module</span>&nbsp;<span class="IdrisModule">Docs.Deriving</span><br />
<br />
<span class="IdrisKeyword">import</span>&nbsp;<span class="IdrisModule">Data.String</span><br />
<span class="IdrisKeyword">import</span>&nbsp;<span class="IdrisModule">Generics.Derive</span><br />
<br />
<span class="IdrisKeyword">%language</span>&nbsp;ElabReflection<br />
</code>

Note: At the moment, deriving interface implementations based on
constructor and argument names such as `Show` is not yet supported.
However, this is very high on my todo list, so I except it to be
available very soon.

## Product Types

Product types consist of a single constructor. Here is
an example of a spell in a role playing game (casting costs
plus the spell's name).

<code class="IdrisCode">
<span class="IdrisKeyword">data</span>&nbsp;<span class="IdrisType">Spell</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">MkSpell</span>&nbsp;<span class="IdrisType">Nat</span>&nbsp;<span class="IdrisType">String</span><br />
</code>

Deriving the most common interface implementations is
straight forward (make sure to import `Generics.Derive`
and enable `%language ElabReflection`):

<code class="IdrisCode">
<span class="IdrisKeyword">%runElab</span>&nbsp;<span class="IdrisFunction">derive</span>&nbsp;<span class="IdrisData">&quot;Spell&quot;</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisFunction">Generic</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Eq</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Ord</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">DecEq</span><span class="IdrisData">]</span><br />
</code>

We can quickly write down some tests:

<code class="IdrisCode">
<span class="IdrisFunction">spellEq1</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisData">MkSpell</span>&nbsp;<span class="IdrisData">12</span>&nbsp;<span class="IdrisData">&quot;foo&quot;</span>&nbsp;<span class="IdrisFunction">==</span>&nbsp;<span class="IdrisData">MkSpell</span>&nbsp;<span class="IdrisData">12</span>&nbsp;<span class="IdrisData">&quot;foo&quot;</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">True</span><br />
<span class="IdrisFunction">spellEq1</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
<br />
<span class="IdrisFunction">spellOrd1</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisData">MkSpell</span>&nbsp;<span class="IdrisData">120</span>&nbsp;<span class="IdrisData">&quot;&quot;</span>&nbsp;<span class="IdrisFunction">&gt;</span>&nbsp;<span class="IdrisData">MkSpell</span>&nbsp;<span class="IdrisData">12</span>&nbsp;<span class="IdrisData">&quot;&quot;</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">True</span><br />
<span class="IdrisFunction">spellOrd1</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
</code>

The library also supports additional forms of
product types.

Records:

<code class="IdrisCode">
<span class="IdrisKeyword">record</span>&nbsp;<span class="IdrisType">Dragon</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;constructor&nbsp;<span class="IdrisData">MkDragon</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">name</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">String</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">hintPoints</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Int</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">spells</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">Spell</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">treasure</span>&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span><br />
<br />
<span class="IdrisKeyword">%runElab</span>&nbsp;<span class="IdrisFunction">derive</span>&nbsp;<span class="IdrisData">&quot;Dragon&quot;</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisFunction">Generic</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Eq</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Ord</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">DecEq</span><span class="IdrisData">]</span><br />
</code>

Parameterized types:

<code class="IdrisCode">
<span class="IdrisKeyword">record</span>&nbsp;<span class="IdrisType">BarbieDragon</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">treasureTpe</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">f</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Type</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;constructor&nbsp;<span class="IdrisData">MkBarbieDragon</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">nameBD</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisType">String</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">hintPointsBD</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisType">Int</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">spellsBD</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;$&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">Spell</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">treasureBD</span>&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;$&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisBound">treasureTpe</span><br />
<br />
<span class="IdrisKeyword">%runElab</span>&nbsp;<span class="IdrisFunction">derive</span>&nbsp;<span class="IdrisData">&quot;BarbieDragon&quot;</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisFunction">Generic</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Eq</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Ord</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">DecEq</span><span class="IdrisData">]</span><br />
</code>

Recursive types:

<code class="IdrisCode">
<span class="IdrisKeyword">record</span>&nbsp;<span class="IdrisType">Hero</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;constructor&nbsp;<span class="IdrisData">MkHero</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">title</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">String</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">hp</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Int</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">equipment</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">allies</span>&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">Hero</span><br />
<br />
<span class="IdrisKeyword">%runElab</span>&nbsp;<span class="IdrisFunction">derive</span>&nbsp;<span class="IdrisData">&quot;Hero&quot;</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisFunction">Generic</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Eq</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Ord</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">DecEq</span><span class="IdrisData">]</span><br />
</code>

Some implementations like the ones for `Semigroup` or `Monoid` can
only be derived for product types:

<code class="IdrisCode">
<span class="IdrisKeyword">record</span>&nbsp;<span class="IdrisType">Employees</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;constructor&nbsp;<span class="IdrisData">MkEmployees</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">names</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">addresses</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">salaries</span>&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">Double</span><br />
<br />
<span class="IdrisKeyword">%runElab</span>&nbsp;<span class="IdrisFunction">derive</span>&nbsp;<span class="IdrisData">&quot;Employees&quot;</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisFunction">Generic</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Eq</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Ord</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Semigroup</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Monoid</span><span class="IdrisData">]</span><br />
<br />
<span class="IdrisFunction">tableTest</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisData">MkEmployees</span>&nbsp;<span class="IdrisData">[]</span>&nbsp;<span class="IdrisData">[]</span>&nbsp;<span class="IdrisData">[]</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">neutral</span>&nbsp;<span class="IdrisKeyword">{</span><span class="IdrisBound">ty</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisType">Employees</span><span class="IdrisKeyword">}</span><br />
<span class="IdrisFunction">tableTest</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
<br />
<span class="IdrisFunction">tableTest2</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisData">MkEmployees</span>&nbsp;<span class="IdrisData">[&quot;a&quot;]</span>&nbsp;<span class="IdrisData">[]</span>&nbsp;<span class="IdrisData">[1]</span>&nbsp;<span class="IdrisFunction">&lt;+&gt;</span>&nbsp;<span class="IdrisData">MkEmployees</span>&nbsp;<span class="IdrisData">[&quot;a&quot;]</span>&nbsp;<span class="IdrisData">[&quot;b&quot;]</span>&nbsp;<span class="IdrisData">[2,3]</span>&nbsp;<span class="IdrisKeyword">=</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisData">MkEmployees</span>&nbsp;<span class="IdrisData">[&quot;a&quot;,&quot;a&quot;]</span>&nbsp;<span class="IdrisData">[&quot;b&quot;]</span>&nbsp;<span class="IdrisData">[1,2,3]</span><br />
<span class="IdrisFunction">tableTest2</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
</code>

## Sum Types

Sum types have more than one constructor but other than that,
deriving instances for them is just as easy as for products:

<code class="IdrisCode">
<span class="IdrisKeyword">data</span>&nbsp;<span class="IdrisType">Monster</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisData">Goblin</span>&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">hp</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Int</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">name</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">String</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Monster</span><br />
&nbsp;&nbsp;<span class="IdrisData">Demon</span>&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">hp</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Int</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">sp</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Int</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">spells</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">Spell</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Monster</span><br />
&nbsp;&nbsp;<span class="IdrisData">Skeleton</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">hp</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Int</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">armor</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Int</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Monster</span><br />
<br />
<span class="IdrisKeyword">%runElab</span>&nbsp;<span class="IdrisFunction">derive</span>&nbsp;<span class="IdrisData">&quot;Monster&quot;</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisFunction">Generic</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Eq</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Ord</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">DecEq</span><span class="IdrisData">]</span><br />
</code>

Likewise, parameterized and inductive types are supported
as well:

<code class="IdrisCode">
<span class="IdrisKeyword">data</span>&nbsp;<span class="IdrisType">Treasure</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisData">Coins</span>&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">value</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Nat</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Treasure</span><br />
&nbsp;&nbsp;<span class="IdrisData">Jewels</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">types</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Nat,String</span><span class="IdrisKeyword">))</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Treasure</span><br />
&nbsp;&nbsp;<span class="IdrisData">Chest</span>&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">content</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">Treasure</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Treasure</span><br />
<br />
<span class="IdrisKeyword">%runElab</span>&nbsp;<span class="IdrisFunction">derive</span>&nbsp;<span class="IdrisData">&quot;Treasure&quot;</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisFunction">Generic</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Eq</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Ord</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">DecEq</span><span class="IdrisData">]</span><br />
</code>

## Deriving Implementations for your own Interfaces

As a fully worked out example, in this part we are going to
implement basic interfaces
for encoding and decoding values to and from lists of string tokens.
These tokens could for instance represent the fields on a single line
of a .csv file.

To keep things simple, we quickly write our own very basic
parser type.

### A Simple Parser for Decoding Lists of Strings

<code class="IdrisCode">
<span class="IdrisComment">|||&nbsp;Tries&nbsp;to&nbsp;convert&nbsp;parts&nbsp;of&nbsp;a&nbsp;list&nbsp;of&nbsp;string&nbsp;tokens</span><br />
<span class="IdrisComment">|||&nbsp;returning&nbsp;either&nbsp;the&nbsp;result&nbsp;plus&nbsp;the&nbsp;remainder</span><br />
<span class="IdrisComment">|||&nbsp;of&nbsp;the&nbsp;list&nbsp;or&nbsp;the&nbsp;remainder&nbsp;of&nbsp;the&nbsp;list&nbsp;where&nbsp;parsing&nbsp;failed.</span><br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisKeyword">record</span>&nbsp;<span class="IdrisType">Parser</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">t</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;constructor&nbsp;<span class="IdrisData">MkParser</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">run</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Either</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">t</span><span class="IdrisType">,</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span><span class="IdrisKeyword">)</span><br />
<br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisType">Functor</span>&nbsp;<span class="IdrisType">Parser</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">map</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">pa</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">MkParser</span>&nbsp;$&nbsp;<span class="IdrisKeyword">\</span><span class="IdrisBound">ts</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisKeyword">do</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">a</span><span class="IdrisData">,</span><span class="IdrisBound">ts&apos;</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">&lt;-</span>&nbsp;<span class="IdrisBound">pa</span><span class="IdrisFunction">.run</span>&nbsp;<span class="IdrisBound">ts</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">pure</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">a</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisBound">ts&apos;</span><span class="IdrisKeyword">)</span><br />
<br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisType">Applicative</span>&nbsp;<span class="IdrisType">Parser</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">pure</span>&nbsp;<span class="IdrisBound">a</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">MkParser</span>&nbsp;$&nbsp;<span class="IdrisKeyword">\</span><span class="IdrisBound">ts</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisData">Right</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">a</span><span class="IdrisData">,</span><span class="IdrisBound">ts</span><span class="IdrisKeyword">)</span><br />
<br />
&nbsp;&nbsp;<span class="IdrisBound">pf</span>&nbsp;<span class="IdrisFunction">&lt;\*&gt;</span>&nbsp;<span class="IdrisBound">pa</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">MkParser</span>&nbsp;$&nbsp;<span class="IdrisKeyword">\</span><span class="IdrisBound">ts</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisKeyword">do</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">f</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisBound">ts&apos;</span>&nbsp;<span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">&lt;-</span>&nbsp;<span class="IdrisBound">pf</span><span class="IdrisFunction">.run</span>&nbsp;<span class="IdrisBound">ts</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">a</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisBound">ts&apos;&apos;</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">&lt;-</span>&nbsp;<span class="IdrisBound">pa</span><span class="IdrisFunction">.run</span>&nbsp;<span class="IdrisBound">ts&apos;</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">pure</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">a</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisBound">ts&apos;&apos;</span><span class="IdrisKeyword">)</span><br />
<br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisType">Monad</span>&nbsp;<span class="IdrisType">Parser</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisBound">pa</span>&nbsp;<span class="IdrisFunction">&gt;&gt;=</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">MkParser</span>&nbsp;$&nbsp;<span class="IdrisKeyword">\</span><span class="IdrisBound">ts</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisKeyword">do</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">a</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisBound">ts&apos;</span>&nbsp;<span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">&lt;-</span>&nbsp;<span class="IdrisBound">pa</span><span class="IdrisFunction">.run</span>&nbsp;<span class="IdrisBound">ts</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">a</span><span class="IdrisKeyword">)</span><span class="IdrisFunction">.run</span>&nbsp;<span class="IdrisBound">ts&apos;</span><br />
<br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisType">Alternative</span>&nbsp;<span class="IdrisType">Parser</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">empty</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">MkParser</span>&nbsp;<span class="IdrisData">Left</span><br />
<br />
&nbsp;&nbsp;<span class="IdrisBound">p1</span>&nbsp;<span class="IdrisFunction">&lt;|&gt;</span>&nbsp;<span class="IdrisBound">p2</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">MkParser</span>&nbsp;$&nbsp;<span class="IdrisKeyword">\</span><span class="IdrisBound">ts</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisKeyword">case</span>&nbsp;<span class="IdrisBound">p1</span><span class="IdrisFunction">.run</span>&nbsp;<span class="IdrisBound">ts</span>&nbsp;<span class="IdrisKeyword">of</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisData">Left</span>&nbsp;<span class="IdrisKeyword">\_</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisBound">p2</span><span class="IdrisFunction">.run</span>&nbsp;<span class="IdrisBound">ts</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisBound">res</span>&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisBound">res</span><br />
<br />
<span class="IdrisComment">|||&nbsp;Returns&nbsp;the&nbsp;next&nbsp;string&nbsp;token,&nbsp;failing&nbsp;if</span><br />
<span class="IdrisComment">|||&nbsp;the&nbsp;list&nbsp;of&nbsp;tokens&nbsp;is&nbsp;empty.</span><br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisFunction">next</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Parser</span>&nbsp;<span class="IdrisType">String</span><br />
<span class="IdrisFunction">next</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">MkParser</span>&nbsp;$&nbsp;<span class="IdrisKeyword">\</span><span class="IdrisBound">ts</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisKeyword">case</span>&nbsp;<span class="IdrisBound">ts</span>&nbsp;<span class="IdrisKeyword">of</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisData">[]</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisData">Left</span>&nbsp;<span class="IdrisData">[]</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">h</span><span class="IdrisData">::</span><span class="IdrisBound">t</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisData">Right</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">h</span><span class="IdrisData">,</span><span class="IdrisBound">t</span><span class="IdrisKeyword">)</span><br />
<br />
<span class="IdrisComment">|||&nbsp;Succeeds&nbsp;if&nbsp;the&nbsp;next&nbsp;token&nbsp;matches&nbsp;exactly&nbsp;the</span><br />
<span class="IdrisComment">|||&nbsp;given&nbsp;String.</span><br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisFunction">string</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Parser</span>&nbsp;<span class="IdrisType">()</span><br />
<span class="IdrisFunction">string</span>&nbsp;<span class="IdrisBound">s</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">next</span>&nbsp;<span class="IdrisFunction">&gt;&gt;=</span>&nbsp;<span class="IdrisFunction">guard</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">s</span>&nbsp;<span class="IdrisFunction">==</span><span class="IdrisKeyword">)</span><br />
<br />
<span class="IdrisComment">|||&nbsp;Maps&nbsp;a&nbsp;partial&nbsp;function&nbsp;over&nbsp;the&nbsp;result</span><br />
<span class="IdrisComment">|||&nbsp;of&nbsp;a&nbsp;parser.&nbsp;This&nbsp;fails,&nbsp;if&nbsp;the&nbsp;function&nbsp;returns</span><br />
<span class="IdrisComment">|||&nbsp;`Nothing`-</span><br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisFunction">mapMaybe</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">a</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Maybe</span>&nbsp;<span class="IdrisBound">b</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Parser</span>&nbsp;<span class="IdrisBound">a</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Parser</span>&nbsp;<span class="IdrisBound">b</span><br />
<span class="IdrisFunction">mapMaybe</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">&gt;&gt;=</span>&nbsp;<span class="IdrisFunction">maybe</span>&nbsp;<span class="IdrisFunction">empty</span>&nbsp;<span class="IdrisFunction">pure</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisBound">f</span><span class="IdrisKeyword">)</span><br />
<br />
<span class="IdrisComment">|||&nbsp;Tries&nbsp;to&nbsp;parse&nbsp;the&nbsp;given&nbsp;number&nbsp;of&nbsp;values.</span><br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisFunction">repeat</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Parser</span>&nbsp;<span class="IdrisBound">a</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Nat</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Parser</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">List</span>&nbsp;<span class="IdrisBound">a</span><span class="IdrisKeyword">)</span><br />
<span class="IdrisFunction">repeat</span>&nbsp;<span class="IdrisKeyword">\_</span>&nbsp;<span class="IdrisData">0</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">pure</span>&nbsp;<span class="IdrisData">[]</span><br />
<span class="IdrisFunction">repeat</span>&nbsp;<span class="IdrisBound">p</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">S</span>&nbsp;<span class="IdrisBound">n</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisKeyword">[|</span>&nbsp;<span class="IdrisBound">p</span>&nbsp;<span class="IdrisData">::</span>&nbsp;<span class="IdrisFunction">repeat</span>&nbsp;<span class="IdrisBound">p</span>&nbsp;<span class="IdrisBound">n</span>&nbsp;<span class="IdrisKeyword">|]</span><br />
<br />
<span class="IdrisComment">|||&nbsp;Runs&nbsp;a&nbsp;parser&nbsp;against&nbsp;a&nbsp;list&nbsp;of&nbsp;string&nbsp;tokens.</span><br />
<span class="IdrisComment">|||&nbsp;Fails&nbsp;if&nbsp;not&nbsp;the&nbsp;whole&nbsp;list&nbsp;is&nbsp;consumed.</span><br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisFunction">parse</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Parser</span>&nbsp;<span class="IdrisBound">t</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Either</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisBound">t</span><br />
<span class="IdrisFunction">parse</span>&nbsp;<span class="IdrisBound">p</span>&nbsp;<span class="IdrisBound">ts</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisKeyword">case</span>&nbsp;<span class="IdrisBound">p</span><span class="IdrisFunction">.run</span>&nbsp;<span class="IdrisBound">ts</span>&nbsp;<span class="IdrisKeyword">of</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisData">Right</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">t</span><span class="IdrisData">,[]</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisData">Right</span>&nbsp;<span class="IdrisBound">t</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisData">Right</span>&nbsp;<span class="IdrisKeyword">(\_</span><span class="IdrisData">,</span><span class="IdrisBound">ts</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisData">Left</span>&nbsp;<span class="IdrisBound">ts</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisData">Left</span>&nbsp;<span class="IdrisBound">ts</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisData">Left</span>&nbsp;<span class="IdrisBound">ts</span><br />
</code>

### Generically derived Encoders

Next, we provide some primitives for encoding values to
lists of string tokens:

<code class="IdrisCode">
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisKeyword">interface</span>&nbsp;<span class="IdrisType">Encode</span>&nbsp;<span class="IdrisBound">t</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;constructor&nbsp;<span class="IdrisData">MkEncode</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisBound">t</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span><br />
<br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisType">Encode</span>&nbsp;<span class="IdrisType">Int</span>&nbsp;<span class="IdrisKeyword">where</span>&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">pure</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisFunction">show</span><br />
<br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisType">Encode</span>&nbsp;<span class="IdrisType">Double</span>&nbsp;<span class="IdrisKeyword">where</span>&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">pure</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisFunction">show</span><br />
<br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisType">Encode</span>&nbsp;<span class="IdrisType">Bool</span>&nbsp;<span class="IdrisKeyword">where</span>&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">pure</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisFunction">show</span><br />
<br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisType">Encode</span>&nbsp;<span class="IdrisType">Nat</span>&nbsp;<span class="IdrisKeyword">where</span>&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">pure</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisFunction">show</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisFunction">cast</span>&nbsp;<span class="IdrisKeyword">{</span><span class="IdrisBound">to</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisType">Integer</span><span class="IdrisKeyword">}</span><br />
<br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisType">Encode</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisKeyword">where</span>&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">pure</span><br />
<br />
<span class="IdrisComment">|||&nbsp;Encoded&nbsp;lists&nbsp;are&nbsp;prefixed&nbsp;with&nbsp;an&nbsp;ecoding&nbsp;of</span><br />
<span class="IdrisComment">|||&nbsp;the&nbsp;number&nbsp;of&nbsp;elements</span><br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisType">Encode</span>&nbsp;<span class="IdrisBound">a</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">Encode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">List</span>&nbsp;<span class="IdrisBound">a</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisBound">as</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">length</span>&nbsp;<span class="IdrisBound">as</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisFunction">++</span>&nbsp;<span class="IdrisFunction">concatMap</span>&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisBound">as</span><br />
</code>

Now, we need an instance for products. As a prerequisite, we
require every element in an n-ary product to have an
instance of `Encode`. We can use an implicit value of
type `NP (Encode . f) ks` to formulate this prerequisite.
This allows us to either implement `encode` by pattern matching
on the product we'd like to encode or by using some
of the combinators provided by this library. `hcmap` followed
by `hconcat` will do the job:

<code class="IdrisCode">
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisFunction">NP</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Encode</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisBound">f</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisBound">ks</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">Encode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">NP</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">ks</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">hconcat</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisFunction">hcmap</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Encode</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisBound">f</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisFunction">encode</span><br />
<br />
</code>

The same goes for n-ary sums. Here, as a precondition, we only
accept single constructor sums, otherwise we'd had
to somehow encode the constructor as a prefix to the remainder
of the list. This can be done by using the `SingletonList`
predicate from `Data.SOP.Utils`.
Otherwise, the implementation uses exactly the same combinators
as the one for `NP`.


<code class="IdrisCode">
<span class="IdrisFunction">NP</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Encode</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisBound">f</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisBound">ks</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">SingletonList</span>&nbsp;<span class="IdrisBound">ks</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">Encode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">NS</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">ks</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">hconcat</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisFunction">hcmap</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Encode</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisBound">f</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisFunction">encode</span><br />
</code>

From the above, we can directly derive instances
for products of products and sums of products.

<code class="IdrisCode">
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisFunction">POP</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Encode</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisBound">f</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisBound">kss</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">Encode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">POP</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">kss</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">MkPOP</span>&nbsp;<span class="IdrisBound">nps</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisBound">nps</span><br />
<br />
<span class="IdrisFunction">POP</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Encode</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisBound">f</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisBound">kss</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">SingletonList</span>&nbsp;<span class="IdrisBound">kss</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">Encode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">SOP</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">kss</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">MkSOP</span>&nbsp;<span class="IdrisBound">v</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisBound">v</span><br />
</code>

Note that in the case of a sum type, we still need the corresponding
product type as a witnesses that we have interface implementations
for all possible fields of the sum.

Next, we define a generic version of `encode`:

<code class="IdrisCode">
<span class="IdrisFunction">genEncode</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;&nbsp;<span class="IdrisType">Generic</span>&nbsp;<span class="IdrisBound">t</span>&nbsp;<span class="IdrisBound">code</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisFunction">POP</span>&nbsp;<span class="IdrisType">Encode</span>&nbsp;<span class="IdrisBound">code</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">SingletonList</span>&nbsp;<span class="IdrisBound">code</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisBound">t</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span><br />
<span class="IdrisFunction">genEncode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisFunction">from</span><br />
</code>

Just as we like it: The type declaration takes up far more space
than the actual implementation. :-)

With this, we can already write derived implementations manually:

<code class="IdrisCode">
<span class="IdrisType">Encode</span>&nbsp;<span class="IdrisType">Spell</span>&nbsp;<span class="IdrisKeyword">where</span>&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">genEncode</span><br />
<br />
<span class="IdrisComment">|||&nbsp;The&nbsp;result&nbsp;can&apos;t&nbsp;be&nbsp;reduced&nbsp;any&nbsp;further,&nbsp;since&nbsp;`show`&nbsp;and</span><br />
<span class="IdrisComment">|||&nbsp;`cast`&nbsp;of&nbsp;primitives&nbsp;is&nbsp;involved.</span><br />
<span class="IdrisFunction">encodeSpellTest</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">MkSpell</span>&nbsp;<span class="IdrisData">10</span>&nbsp;<span class="IdrisData">&quot;foo&quot;</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisData">[</span><span class="IdrisFunction">show</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">cast</span>&nbsp;<span class="IdrisKeyword">{</span><span class="IdrisBound">from</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisType">Nat</span><span class="IdrisKeyword">}</span>&nbsp;<span class="IdrisKeyword">{</span><span class="IdrisBound">to</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisType">Integer</span><span class="IdrisKeyword">}</span>&nbsp;<span class="IdrisData">10</span><span class="IdrisKeyword">)</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisData">&quot;foo&quot;]</span><br />
<span class="IdrisFunction">encodeSpellTest</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Refl</span><br />
</code>

In order to make the interface available to function `derive`,
we have to write a minimal amount of reflection code:

<code class="IdrisCode">
<span class="IdrisComment">|||&nbsp;Derives&nbsp;an&nbsp;`Encode`&nbsp;implementation&nbsp;for&nbsp;the&nbsp;given&nbsp;data&nbsp;type</span><br />
<span class="IdrisComment">|||&nbsp;and&nbsp;visibility.</span><br />
<span class="IdrisFunction">EncodeVis</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Visibility</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">DeriveUtil</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">InterfaceImpl</span><br />
<span class="IdrisFunction">EncodeVis</span>&nbsp;<span class="IdrisBound">vis</span>&nbsp;<span class="IdrisBound">g</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">MkInterfaceImpl</span>&nbsp;<span class="IdrisData">&quot;Encode&quot;</span>&nbsp;<span class="IdrisBound">vis</span>&nbsp;<span class="IdrisData">[]</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">`(</span><span class="IdrisData">MkEncode</span>&nbsp;<span class="IdrisFunction">genEncode</span><span class="IdrisKeyword">)</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">implementationType</span>&nbsp;<span class="IdrisKeyword">`(</span><span class="IdrisType">Encode</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisBound">g</span><span class="IdrisKeyword">)</span><br />
<br />
<span class="IdrisComment">|||&nbsp;Alias&nbsp;for&nbsp;`EncodeVis&nbsp;Public`.</span><br />
<span class="IdrisFunction">Encode&apos;</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">DeriveUtil</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">InterfaceImpl</span><br />
<span class="IdrisFunction">Encode&apos;</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">EncodeVis</span>&nbsp;<span class="IdrisData">Public</span><br />
</code>

Let's encode us some dragons:

<code class="IdrisCode">
<span class="IdrisKeyword">%runElab</span>&nbsp;<span class="IdrisFunction">derive</span>&nbsp;<span class="IdrisData">&quot;Dragon&quot;</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisFunction">Encode&apos;</span><span class="IdrisData">]</span><br />
</code>

### Generically derived Decoders

Deriving decoders is only slightly more involved. First, we
need again some primitives:

<code class="IdrisCode">
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisKeyword">interface</span>&nbsp;<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisBound">t</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;constructor&nbsp;<span class="IdrisData">MkDecode</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Parser</span>&nbsp;<span class="IdrisBound">t</span><br />
<br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisType">Int</span>&nbsp;<span class="IdrisKeyword">where</span>&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">mapMaybe</span>&nbsp;<span class="IdrisFunction">parseInteger</span>&nbsp;<span class="IdrisFunction">next</span><br />
<br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisType">Double</span>&nbsp;<span class="IdrisKeyword">where</span>&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">mapMaybe</span>&nbsp;<span class="IdrisFunction">parseDouble</span>&nbsp;<span class="IdrisFunction">next</span><br />
<br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisType">Bool</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">mapMaybe</span>&nbsp;<span class="IdrisFunction">parseBool</span>&nbsp;<span class="IdrisFunction">next</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">where</span>&nbsp;<span class="IdrisFunction">parseBool</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Maybe</span>&nbsp;<span class="IdrisType">Bool</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">parseBool</span>&nbsp;<span class="IdrisData">&quot;False&quot;</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Just</span>&nbsp;<span class="IdrisData">False</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">parseBool</span>&nbsp;<span class="IdrisData">&quot;True&quot;</span>&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Just</span>&nbsp;<span class="IdrisData">True</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">parseBool</span>&nbsp;<span class="IdrisKeyword">\_</span>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Nothing</span><br />
<br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisType">Nat</span>&nbsp;<span class="IdrisKeyword">where</span>&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">mapMaybe</span>&nbsp;<span class="IdrisFunction">parsePositive</span>&nbsp;<span class="IdrisFunction">next</span><br />
<br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisType">String</span>&nbsp;<span class="IdrisKeyword">where</span>&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">next</span><br />
<br />
<span class="IdrisComment">|||&nbsp;First,&nbsp;the&nbsp;number&nbsp;of&nbsp;elements&nbsp;is&nbsp;decoded,&nbsp;followed</span><br />
<span class="IdrisComment">|||&nbsp;by&nbsp;a&nbsp;repeated&nbsp;application&nbsp;of&nbsp;the&nbsp;element&nbsp;Decoder.</span><br />
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisBound">a</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">List</span>&nbsp;<span class="IdrisBound">a</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisFunction">&gt;&gt;=</span>&nbsp;<span class="IdrisFunction">repeat</span>&nbsp;<span class="IdrisFunction">decode</span><br />
</code>

Now come the decoders for n-ary products.
We can use `hcpure` and `hsequence` for this:

<code class="IdrisCode">
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisFunction">NP</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Decode</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisBound">f</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisBound">ks</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">NP</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">ks</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">hsequence</span>&nbsp;$&nbsp;<span class="IdrisFunction">hcpure</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Decode</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisBound">f</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisFunction">decode</span><br />
</code>

For sums, we once again allow only sums representing
types with a single constructor. In this
case we need to pattern match on the implicitly available `Decode` instance
to make it available when decoding the inner
value:

<code class="IdrisCode">
<span class="IdrisKeyword">(</span><span class="IdrisBound">decs</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisFunction">NP</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Decode</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisBound">f</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisBound">ks</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">SingletonList</span>&nbsp;<span class="IdrisBound">ks</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">NS</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">ks</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisKeyword">{</span><span class="IdrisBound">decs</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisKeyword">\_</span>&nbsp;<span class="IdrisData">::</span>&nbsp;<span class="IdrisKeyword">\_</span>&nbsp;<span class="IdrisKeyword">}</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">map</span>&nbsp;<span class="IdrisData">Z</span>&nbsp;<span class="IdrisFunction">decode</span><br />
</code>

Finally, the trivial versions for `POP` and `SOP`:

<code class="IdrisCode">
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisFunction">POP</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Decode</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisBound">f</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisBound">kss</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">POP</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">kss</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">map</span>&nbsp;<span class="IdrisData">MkPOP</span>&nbsp;<span class="IdrisFunction">decode</span><br />
<br />
<span class="IdrisFunction">POP</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Decode</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisBound">f</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisBound">kss</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">SingletonList</span>&nbsp;<span class="IdrisBound">kss</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">SOP</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">kss</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">map</span>&nbsp;<span class="IdrisData">MkSOP</span>&nbsp;<span class="IdrisFunction">decode</span><br />
</code>

And again, we provide a generic version of `decode`:

<code class="IdrisCode">
<span class="IdrisFunction">genDecode</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;&nbsp;<span class="IdrisType">Generic</span>&nbsp;<span class="IdrisBound">t</span>&nbsp;<span class="IdrisBound">code</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisFunction">POP</span>&nbsp;<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisBound">code</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">SingletonList</span>&nbsp;<span class="IdrisBound">code</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">Parser</span>&nbsp;<span class="IdrisBound">t</span><br />
<span class="IdrisFunction">genDecode</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">map</span>&nbsp;<span class="IdrisFunction">to</span>&nbsp;<span class="IdrisFunction">decode</span><br />
</code>

Finally, the necessary reflection code:

<code class="IdrisCode">
<span class="IdrisComment">|||&nbsp;Derives&nbsp;a&nbsp;`Decode`&nbsp;implementation&nbsp;for&nbsp;the&nbsp;given&nbsp;data&nbsp;type</span><br />
<span class="IdrisComment">|||&nbsp;and&nbsp;visibility.</span><br />
<span class="IdrisFunction">DecodeVis</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Visibility</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">DeriveUtil</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">InterfaceImpl</span><br />
<span class="IdrisFunction">DecodeVis</span>&nbsp;<span class="IdrisBound">vis</span>&nbsp;<span class="IdrisBound">g</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">MkInterfaceImpl</span>&nbsp;<span class="IdrisData">&quot;Decode&quot;</span>&nbsp;<span class="IdrisBound">vis</span>&nbsp;<span class="IdrisData">[]</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">`(</span><span class="IdrisData">MkDecode</span>&nbsp;<span class="IdrisFunction">genDecode</span><span class="IdrisKeyword">)</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">implementationType</span>&nbsp;<span class="IdrisKeyword">`(</span><span class="IdrisType">Decode</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisBound">g</span><span class="IdrisKeyword">)</span><br />
<br />
<span class="IdrisComment">|||&nbsp;Alias&nbsp;for&nbsp;`DecodeVis&nbsp;Public`.</span><br />
<span class="IdrisFunction">Decode&apos;</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">DeriveUtil</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">InterfaceImpl</span><br />
<span class="IdrisFunction">Decode&apos;</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">DecodeVis</span>&nbsp;<span class="IdrisData">Public</span><br />
</code>

Let's decode us some dragons:

<code class="IdrisCode">
<span class="IdrisKeyword">%runElab</span>&nbsp;<span class="IdrisFunction">derive</span>&nbsp;<span class="IdrisData">&quot;Spell&quot;</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisFunction">Decode&apos;</span><span class="IdrisData">]</span><br />
<br />
<span class="IdrisKeyword">%runElab</span>&nbsp;<span class="IdrisFunction">derive</span>&nbsp;<span class="IdrisData">&quot;Dragon&quot;</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisFunction">Decode&apos;</span><span class="IdrisData">]</span><br />
</code>

In order to play around with this in the REPL, we need access
to a dragon:

<code class="IdrisCode">
<span class="IdrisKeyword">public</span>&nbsp;<span class="IdrisKeyword">export</span><br />
<span class="IdrisFunction">gorgar</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Dragon</span><br />
<span class="IdrisFunction">gorgar</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">MkDragon</span>&nbsp;<span class="IdrisData">&quot;GORGAR&quot;</span>&nbsp;<span class="IdrisData">15000</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisData">[MkSpell</span>&nbsp;<span class="IdrisData">100</span>&nbsp;<span class="IdrisData">&quot;Fireball&quot;,</span>&nbsp;<span class="IdrisData">MkSpell</span>&nbsp;<span class="IdrisData">20</span>&nbsp;<span class="IdrisData">&quot;Invisibility&quot;]</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisData">[&quot;Mail&nbsp;of&nbsp;Mithril&quot;,</span>&nbsp;<span class="IdrisData">&quot;1&apos;000&nbsp;gold&nbsp;coins&quot;]</span><br />
<br />
<span class="IdrisKeyword">export</span><br />
<span class="IdrisFunction">printGorgar</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">IO</span>&nbsp;<span class="IdrisType">()</span><br />
<span class="IdrisFunction">printGorgar</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">printLn</span>&nbsp;$&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisFunction">gorgar</span><br />
<br />
<span class="IdrisKeyword">export</span><br />
<span class="IdrisFunction">testDecodingGorgar</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">IO</span>&nbsp;<span class="IdrisType">()</span><br />
<span class="IdrisFunction">testDecodingGorgar</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">printLn</span>&nbsp;$&nbsp;<span class="IdrisData">Right</span>&nbsp;<span class="IdrisFunction">gorgar</span>&nbsp;<span class="IdrisFunction">==</span>&nbsp;<span class="IdrisFunction">parse</span>&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisFunction">gorgar</span><span class="IdrisKeyword">)</span><br />
</code>

## Conclusion

This post demonstrated the most important aspects of deriving
interface implementations automatically from generic representations
of data types as well as the most basic pieces of reflection
code necessary to make interfaces available to `derive`.
For a much more thorough introduction to the concepts and code
behind `derive`, see the tutorials on *Generics* at
the [idris2-elab-util](https://github.com/stefan-hoeck/idris2-elab-util)
package.

In the [next part](Metadata.md), we are going to enhance our
encoders and decoders to properly support sum types. For this,
we will need access to a data type's metadata like
constructor and argument names.

