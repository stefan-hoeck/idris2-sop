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
# Metadata

In the [last part](Deriving.md) of the tutorial, we experimented with
automatically deriving different interface implementations. Those
examples could be derived directly from a data type's type-level
code without the need for additional information.

For some interfaces like `Show`, however, this is not enough: In order
to derive a `Show` instance, we need to know about constructor names and
possibly record field names. In this part of the tutorial we learn how to
get access to those and how to make use of this information
to enhance our own `Encoder` and `Decoder` interfaces from the
last part.

<code class="IdrisCode">
<span class="IdrisKeyword">module</span>&nbsp;<span class="IdrisModule">Docs.Metadata</span><br />
<br />
<span class="IdrisKeyword">import</span>&nbsp;<span class="IdrisModule">Generics.Derive</span><br />
<span class="IdrisKeyword">import</span>&nbsp;<span class="IdrisModule">Docs.Deriving</span><br />
<br />
<span class="IdrisKeyword">%language</span>&nbsp;ElabReflection<br />
</code>

## `Meta`: An Interface for Metadata

Getting access to a data type's metadata is as simple as deriving
its `Meta` interface (from module `Generics.Meta`). This gives us access
to functions `meta` and `metaFor`, both of which return a `TypeInfo`
record, wrapping a product of `ConInfo` values.
Like `SOP`, `TypeInfo` is indexed over a list of lists of values to
match the structure of the generic code of a data type.

Before we learn how to use metadata to write our own interface
implementations, here are two data types with automatically
derived `Meta` and `Show` implementations (we have to use fully
qualified names, because module `Docs.Deriving` contains private data types
with identical names, which seems to confuse Idris):

<code class="IdrisCode">
<span class="IdrisKeyword">export</span><br />
<span class="IdrisKeyword">data</span>&nbsp;<span class="IdrisType">Spell</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">MkSpell</span>&nbsp;<span class="IdrisType">Nat</span>&nbsp;<span class="IdrisType">String</span><br />
<br />
<span class="IdrisKeyword">%runElab</span>&nbsp;<span class="IdrisFunction">derive</span>&nbsp;<span class="IdrisData">&quot;Docs.Metadata.Spell&quot;</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisFunction">Generic</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Meta</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Eq</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Ord</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">DecEq</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Show</span><span class="IdrisData">]</span><br />
<br />
<span class="IdrisKeyword">export</span><br />
<span class="IdrisKeyword">data</span>&nbsp;<span class="IdrisType">Monster</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Type</span>&nbsp;<span class="IdrisKeyword">where</span><br />
&nbsp;&nbsp;<span class="IdrisData">Goblin</span>&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">hp</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Int</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">name</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">String</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Monster</span><br />
&nbsp;&nbsp;<span class="IdrisData">Demon</span>&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">hp</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Int</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">sp</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Int</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">spells</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">Spell</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Monster</span><br />
&nbsp;&nbsp;<span class="IdrisData">Skeleton</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">hp</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Int</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">armor</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Int</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Monster</span><br />
<br />
<span class="IdrisKeyword">%runElab</span>&nbsp;<span class="IdrisFunction">derive</span>&nbsp;<span class="IdrisData">&quot;Docs.Metadata.Monster&quot;</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisFunction">Generic</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Meta</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Eq</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Ord</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">DecEq</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Show</span><span class="IdrisData">]</span><br />
</code>

## An `Encoder` for Sum Types

So far, we only supported the deriving of decoders for product
types. We'd like to also support sum types, by prefixing encodings
with the corresponding constructor's name:

<code class="IdrisCode">
<span class="IdrisFunction">encodeCon</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Encode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">NP</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">ks</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisFunction">ConInfo</span>&nbsp;<span class="IdrisBound">ks</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">NP</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">ks</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span><br />
<span class="IdrisFunction">encodeCon</span>&nbsp;<span class="IdrisBound">ci</span>&nbsp;<span class="IdrisBound">np</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisBound">ci</span><span class="IdrisFunction">.conName</span>&nbsp;<span class="IdrisData">::</span>&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisBound">np</span><br />
</code>

Since a type's constructors are wrapped in an `NP` parameterized
by the same type level list as its generic representation,
we can use the usual SOP combinators to generate an
encoding for a `SOP` value. As can be guessed from the type of `encodeCon`
we can use `hcliftA2` followed by `hconcat`:

<code class="IdrisCode">
<span class="IdrisFunction">genEncode</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Meta</span>&nbsp;<span class="IdrisBound">t</span>&nbsp;<span class="IdrisBound">code</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">all</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisFunction">POP</span>&nbsp;<span class="IdrisType">Encode</span>&nbsp;<span class="IdrisBound">code</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisBound">t</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span><br />
<span class="IdrisFunction">genEncode</span>&nbsp;<span class="IdrisKeyword">{</span><span class="IdrisBound">all</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">MkPOP</span>&nbsp;<span class="IdrisKeyword">\_}</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">encodeSOP</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">metaFor</span>&nbsp;<span class="IdrisBound">t</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisFunction">from</span><br />
&nbsp;&nbsp;<span class="IdrisKeyword">where</span>&nbsp;<span class="IdrisFunction">encodeSOP</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisFunction">TypeInfo</span>&nbsp;<span class="IdrisBound">code</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">SOP</span>&nbsp;<span class="IdrisFunction">I</span>&nbsp;<span class="IdrisBound">code</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">encodeSOP</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">MkTypeInfo</span>&nbsp;<span class="IdrisKeyword">\_</span>&nbsp;<span class="IdrisKeyword">\_</span>&nbsp;<span class="IdrisBound">cons</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">hconcat</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisFunction">hcliftA2</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Encode</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisFunction">NP</span>&nbsp;<span class="IdrisFunction">I</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisFunction">encodeCon</span>&nbsp;<span class="IdrisBound">cons</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisFunction">unSOP</span><br />
</code>

The functions to be used in `derive` are verbatim copies of the
ones used in the last post, but they call a different version
of `genEncode`, therefore we have to include them here:

<code class="IdrisCode">
<br />
<span class="IdrisFunction">EncodeVis</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Visibility</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">DeriveUtil</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">InterfaceImpl</span><br />
<span class="IdrisFunction">EncodeVis</span>&nbsp;<span class="IdrisBound">vis</span>&nbsp;<span class="IdrisBound">g</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">MkInterfaceImpl</span>&nbsp;<span class="IdrisData">&quot;Encode&quot;</span>&nbsp;<span class="IdrisBound">vis</span>&nbsp;<span class="IdrisData">[]</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">`(</span><span class="IdrisData">MkEncode</span>&nbsp;<span class="IdrisFunction">genEncode</span><span class="IdrisKeyword">)</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">implementationType</span>&nbsp;<span class="IdrisKeyword">`(</span><span class="IdrisType">Encode</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisBound">g</span><span class="IdrisKeyword">)</span><br />
<br />
<span class="IdrisFunction">Encode&apos;</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">DeriveUtil</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">InterfaceImpl</span><br />
<span class="IdrisFunction">Encode&apos;</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">EncodeVis</span>&nbsp;<span class="IdrisData">Public</span><br />
</code>

## Decoding Sum Types: A Use Case for `injections`

We will need a new SOP technique for decoding sum types.
But first, decoding a single constructor seems to be straight
forward: We read the expected constructor name before
decoding the arguments.
However, as can be seen in the implementation of `decodeCon`
we somehow need to convert the decoded n-ary sum to a `SOP`
value by applying the correct sequence of `S` and `Z` constructors:

<code class="IdrisCode">
<span class="IdrisFunction">decodeCon</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;&nbsp;<span class="IdrisKeyword">forall</span>&nbsp;<span class="IdrisBound">ks</span>&nbsp;<span class="IdrisKeyword">.</span>&nbsp;<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">NP</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">ks</span><span class="IdrisKeyword">)</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisFunction">ConInfo</span>&nbsp;<span class="IdrisBound">ks</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">toSOP</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisFunction">NP</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">ks</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisFunction">SOP</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">kss</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Parser</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">SOP</span>&nbsp;<span class="IdrisBound">f</span>&nbsp;<span class="IdrisBound">kss</span><span class="IdrisKeyword">)</span><br />
<span class="IdrisFunction">decodeCon</span>&nbsp;<span class="IdrisBound">ci</span>&nbsp;<span class="IdrisBound">toSOP</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">string</span>&nbsp;<span class="IdrisBound">ci</span><span class="IdrisFunction">.conName</span>&nbsp;<span class="IdrisFunction">\*&gt;</span>&nbsp;<span class="IdrisFunction">map</span>&nbsp;<span class="IdrisBound">toSOP</span>&nbsp;<span class="IdrisFunction">decode</span><br />
</code>

Function `toSOP` is called an *injection* into the n-ary sum. Module *Data.SOP*
provides function `injectionsSOP`, returning an n-ary product of all
injections from n-ary products into a sum of products parameterized over
the given typelevel list of lists. In order to combine the resulting
n-ary product of parsers, we use function `hchoice` making use of
the `Alternative` instance of `Parser`:

<code class="IdrisCode">
<span class="IdrisComment">--&nbsp;Generic&nbsp;decoding&nbsp;function</span><br />
<span class="IdrisFunction">genDecode</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">{</span><span class="IdrisBound">code</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisKeyword">\_}</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Meta</span>&nbsp;<span class="IdrisBound">t</span>&nbsp;<span class="IdrisBound">code</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisBound">all</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisFunction">POP</span>&nbsp;<span class="IdrisType">Decode</span>&nbsp;<span class="IdrisBound">code</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=&gt;</span>&nbsp;<span class="IdrisType">Parser</span>&nbsp;<span class="IdrisBound">t</span><br />
<span class="IdrisFunction">genDecode</span>&nbsp;<span class="IdrisKeyword">{</span><span class="IdrisBound">all</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">MkPOP</span>&nbsp;<span class="IdrisKeyword">\_}</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">to</span>&nbsp;<span class="IdrisFunction">&lt;$&gt;</span>&nbsp;<span class="IdrisFunction">decodeSOP</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">metaFor</span>&nbsp;<span class="IdrisBound">t</span><span class="IdrisKeyword">)</span><br />
&nbsp;&nbsp;<span class="IdrisKeyword">where</span>&nbsp;<span class="IdrisFunction">decodeSOP</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisFunction">TypeInfo</span>&nbsp;<span class="IdrisBound">code</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">Parser</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">SOP</span>&nbsp;<span class="IdrisFunction">I</span>&nbsp;<span class="IdrisBound">code</span><span class="IdrisKeyword">)</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">decodeSOP</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisData">MkTypeInfo</span>&nbsp;<span class="IdrisKeyword">\_</span>&nbsp;<span class="IdrisKeyword">\_</span>&nbsp;<span class="IdrisBound">cons</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisKeyword">=</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisFunction">hchoice</span>&nbsp;$&nbsp;<span class="IdrisFunction">hcliftA2</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">Decode</span>&nbsp;<span class="IdrisFunction">.</span>&nbsp;<span class="IdrisFunction">NP</span>&nbsp;<span class="IdrisFunction">I</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisFunction">decodeCon</span>&nbsp;<span class="IdrisBound">cons</span>&nbsp;<span class="IdrisFunction">injectionsSOP</span><br />
</code>

Again, the functions to be used in `derive` are verbatim copies of the
ones used in the last post:


<code class="IdrisCode">
<span class="IdrisFunction">DecodeVis</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Visibility</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">DeriveUtil</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">InterfaceImpl</span><br />
<span class="IdrisFunction">DecodeVis</span>&nbsp;<span class="IdrisBound">vis</span>&nbsp;<span class="IdrisBound">g</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">MkInterfaceImpl</span>&nbsp;<span class="IdrisData">&quot;Decode&quot;</span>&nbsp;<span class="IdrisBound">vis</span>&nbsp;<span class="IdrisData">[]</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">`(</span><span class="IdrisData">MkDecode</span>&nbsp;<span class="IdrisFunction">genDecode</span><span class="IdrisKeyword">)</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisFunction">implementationType</span>&nbsp;<span class="IdrisKeyword">`(</span><span class="IdrisType">Decode</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisBound">g</span><span class="IdrisKeyword">)</span><br />
<br />
<span class="IdrisFunction">Decode&apos;</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">DeriveUtil</span>&nbsp;<span class="IdrisKeyword">-&gt;</span>&nbsp;<span class="IdrisType">InterfaceImpl</span><br />
<span class="IdrisFunction">Decode&apos;</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">DecodeVis</span>&nbsp;<span class="IdrisData">Public</span><br />
</code>

We can now derive encoders and decoders for `Monster`s and
test them at the REPL:

<code class="IdrisCode">
<span class="IdrisKeyword">%runElab</span>&nbsp;<span class="IdrisFunction">derive</span>&nbsp;<span class="IdrisData">&quot;Docs.Metadata.Spell&quot;</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisFunction">Encode&apos;</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Decode&apos;</span><span class="IdrisData">]</span><br />
<br />
<span class="IdrisKeyword">%runElab</span>&nbsp;<span class="IdrisFunction">derive</span>&nbsp;<span class="IdrisData">&quot;Docs.Metadata.Monster&quot;</span>&nbsp;<span class="IdrisData">[</span><span class="IdrisFunction">Encode&apos;</span><span class="IdrisData">,</span>&nbsp;<span class="IdrisFunction">Decode&apos;</span><span class="IdrisData">]</span><br />
<br />
<span class="IdrisKeyword">export</span><br />
<span class="IdrisFunction">demon</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Monster</span><br />
<span class="IdrisFunction">demon</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">Demon</span>&nbsp;<span class="IdrisKeyword">{</span>&nbsp;<span class="IdrisBound">hp</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">530</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">,</span>&nbsp;<span class="IdrisBound">sp</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">120</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">,</span>&nbsp;<span class="IdrisBound">spells</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisData">[MkSpell</span>&nbsp;<span class="IdrisData">40</span>&nbsp;<span class="IdrisData">&quot;Disintegrate&quot;,</span>&nbsp;<span class="IdrisData">MkSpell</span>&nbsp;<span class="IdrisData">10</span>&nbsp;<span class="IdrisData">&quot;Utterdark&quot;]</span><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="IdrisKeyword">}</span><br />
<br />
<span class="IdrisKeyword">export</span><br />
<span class="IdrisFunction">encDemon</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span><br />
<span class="IdrisFunction">encDemon</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">encode</span>&nbsp;<span class="IdrisFunction">demon</span><br />
<br />
<span class="IdrisKeyword">export</span><br />
<span class="IdrisFunction">decDemon</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">Either</span>&nbsp;<span class="IdrisKeyword">(</span><span class="IdrisType">List</span>&nbsp;<span class="IdrisType">String</span><span class="IdrisKeyword">)</span>&nbsp;<span class="IdrisType">Monster</span><br />
<span class="IdrisFunction">decDemon</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">parse</span>&nbsp;<span class="IdrisFunction">decode</span>&nbsp;<span class="IdrisFunction">encDemon</span><br />
<br />
<span class="IdrisKeyword">export</span><br />
<span class="IdrisFunction">printDecDemon</span>&nbsp;<span class="IdrisKeyword">:</span>&nbsp;<span class="IdrisType">IO</span>&nbsp;<span class="IdrisType">()</span><br />
<span class="IdrisFunction">printDecDemon</span>&nbsp;<span class="IdrisKeyword">=</span>&nbsp;<span class="IdrisFunction">printLn</span>&nbsp;<span class="IdrisFunction">decDemon</span><br />
</code>

## Conclusion

Again, the SOP approach provides powerful abstraction to write
generic interface implementations. This post completes the part
about deriving interface implementations. Still, there are other
possibilities and techniques of this library to explore, for
instance the ability to provide automatically
generated lenses.

