---
src       : src/plfa/Equality.lagda
title     : "Equality: 相等性与等式推理"
layout    : page
prev      : /Relations/
permalink : /Equality/
next      : /Isomorphism/
translators : ["Fangyi Zhou"]
progress  : 100
---

<pre class="Agda">{% raw %}<a id="192" class="Keyword">module</a> <a id="199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}" class="Module">plfa.Equality</a> <a id="213" class="Keyword">where</a>{% endraw %}</pre>

我们在论证的过程中经常会使用相等性。给定两个都为 `A` 类型的项 `M` 和 `N`，
我们用 `M ≡ N` 来表示 `M` 和 `N` 可以相互替换。在此之前，
我们将相等性作为一个基础运算，而现在我们来说明如果将其定义为一个归纳的数据类型。

{::comment}
Much of our reasoning has involved equality.  Given two terms `M`
and `N`, both of type `A`, we write `M ≡ N` to assert that `M` and `N`
are interchangeable.  So far we have treated equality as a primitive,
here we show how to define it as an inductive datatype.
{:/}

## 导入
{::comment}
## Imports
{:/}

本章节没有导入的内容。本书的每一章节，以及 Agda 标准库的每个模块都导入了相等性。
我们在此定义相等性，导入其他内容将会产生冲突。

{::comment}
This chapter has no imports.  Every chapter in this book, and nearly
every module in the Agda standard library, imports equality.
Since we define equality here, any import would create a conflict.
{:/}

## 相等性
{::comment}
## Equality
{:/}

我们如下定义相等性：
{::comment}
We declare equality as follows:
{:/}
<pre class="Agda">{% raw %}<a id="1067" class="Keyword">data</a> <a id="_≡_"></a><a id="1072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">_≡_</a> <a id="1076" class="Symbol">{</a><a id="1077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1077" class="Bound">A</a> <a id="1079" class="Symbol">:</a> <a id="1081" class="PrimitiveType">Set</a><a id="1084" class="Symbol">}</a> <a id="1086" class="Symbol">(</a><a id="1087" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1087" class="Bound">x</a> <a id="1089" class="Symbol">:</a> <a id="1091" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1077" class="Bound">A</a><a id="1092" class="Symbol">)</a> <a id="1094" class="Symbol">:</a> <a id="1096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1077" class="Bound">A</a> <a id="1098" class="Symbol">→</a> <a id="1100" class="PrimitiveType">Set</a> <a id="1104" class="Keyword">where</a>
  <a id="_≡_.refl"></a><a id="1112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a> <a id="1117" class="Symbol">:</a> <a id="1119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1087" class="Bound">x</a> <a id="1121" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="1123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1087" class="Bound">x</a>{% endraw %}</pre>

用其他的话来说，对于任意类型 `A` 和任意 `A` 类型的 `x`，构造器 `refl` 提供了
`x ≡ x` 的证明。所以，每个值等同于它本身，我们并没有其他办法来证明值的相等性。
这个定义里有不对称的地方，`_≡_` 的第一个参数（Argument）由 `x : A` 给出，
而第二个参数（Argument）则是由 `A → Set` 的索引给出。
这和我们尽可能多的使用参数（Parameter）的理念相符。`_≡_` 的第一个参数（Argument）
可以作为一个参数（Parameter），因为它不会变，而第二个参数（Argument）则必须是一个索引，
这样它才可以等用于第一个。
{::comment}
In other words, for any type `A` and for any `x` of type `A`, the
constructor `refl` provides evidence that `x ≡ x`. Hence, every value
is equal to itself, and we have no other way of showing values
equal.  The definition features an asymmetry, in that the
first argument to `_≡_` is given by the parameter `x : A`, while the
second is given by an index in `A → Set`.  This follows our policy
of using parameters wherever possible.  The first argument to `_≡_`
can be a parameter because it doesn't vary, while the second must be
an index, so it can be required to be equal to the first.
{:/}

我们如下定义相等性的优先级：
{::comment}
We declare the precedence of equality as follows:
{:/}
<pre class="Agda">{% raw %}<a id="2138" class="Keyword">infix</a> <a id="2144" class="Number">4</a> <a id="2146" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">_≡_</a>{% endraw %}</pre>
我们将 `_≡_` 的优先级设置为 4，与 `_≤_` 相同，所以它没有算术运算符相比结合的紧密。
它既不是左结合，也不是右结合的，因此 `x ≡ y ≡ z` 是不合法的。
{::comment}
We set the precedence of `_≡_` at level 4, the same as `_≤_`,
which means it binds less tightly than any arithmetic operator.
It associates neither to left nor right; writing `x ≡ y ≡ z`
is illegal.
{:/}

## 相等性是一个等价关系（Equivalence Relation）
{::comment}
## Equality is an equivalence relation
{:/}

一个等价关系是自反、对称和传递的。其中自反性可以通过构造器 `refl` 直接从相等性的定义中得来。
我们可以直接地证明其对称性：
{::comment}
An equivalence relation is one which is reflexive, symmetric, and transitive.
Reflexivity is built-in to the definition of equality, via the
constructor `refl`.  It is straightforward to show symmetry:
{:/}
<pre class="Agda">{% raw %}<a id="sym"></a><a id="2857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2857" class="Function">sym</a> <a id="2861" class="Symbol">:</a> <a id="2863" class="Symbol">∀</a> <a id="2865" class="Symbol">{</a><a id="2866" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2866" class="Bound">A</a> <a id="2868" class="Symbol">:</a> <a id="2870" class="PrimitiveType">Set</a><a id="2873" class="Symbol">}</a> <a id="2875" class="Symbol">{</a><a id="2876" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2876" class="Bound">x</a> <a id="2878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2878" class="Bound">y</a> <a id="2880" class="Symbol">:</a> <a id="2882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2866" class="Bound">A</a><a id="2883" class="Symbol">}</a>
  <a id="2887" class="Symbol">→</a> <a id="2889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2876" class="Bound">x</a> <a id="2891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="2893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2878" class="Bound">y</a>
    <a id="2899" class="Comment">-----</a>
  <a id="2907" class="Symbol">→</a> <a id="2909" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2878" class="Bound">y</a> <a id="2911" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="2913" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2876" class="Bound">x</a>
<a id="2915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2857" class="Function">sym</a> <a id="2919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a> <a id="2924" class="Symbol">=</a> <a id="2926" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a>{% endraw %}</pre>
这个证明是怎么运作的呢？`sym` 参数的类型是 `x ≡ y`，但是等式的左手边被 `refl` 模式实例化了，
这要求 `x` 和 `y` 相等。因此，等式的右手边需要一个类型为 `x ≡ x` 的项，用 `refl` 即可。
{::comment}
How does this proof work? The argument to `sym` has type `x ≡ y`, but
on the left-hand side of the equation the argument has been
instantiated to the pattern `refl`, which requires that `x` and `y`
are the same.  Hence, for the right-hand side of the equation we need
a term of type `x ≡ x`, and `refl` will do.
{:/}

交互式地证明 `sym` 很有教育意义。首先，我们在左手边使用一个变量来表示参数，在右手边使用一个洞：
{::comment}
It is instructive to develop `sym` interactively.  To start, we supply
a variable for the argument on the left, and a hole for the body on
the right:
{:/}

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym e = {! !}

如果我们进入这个洞，使用 `C-c C-,`，Agda 会告诉我们：
{::comment}
If we go into the hole and type `C-c C-,` then Agda reports:
{:/}

    Goal: .y ≡ .x
    ————————————————————————————————————————————————————————————
    e  : .x ≡ .y
    .y : .A
    .x : .A
    .A : Set

在这个洞里，我们使用 `C-c C-c e`，Agda 会将 `e` 逐一展开为其所有可能的构造器。
此处只有一个构造器：
{::comment}
If in the hole we type `C-c C-c e` then Agda will instantiate `e` to
all possible constructors, with one equation for each. There is only
one possible constructor:
{:/}

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = {! !}

如果我们再次进入这个洞，重新使用 `C-c C-,`，然后 Agda 现在会告诉我们：
{::comment}
If we go into the hole again and type `C-c C-,` then Agda now reports:
{:/}

     Goal: .x ≡ .x
     ————————————————————————————————————————————————————————————
     .x : .A
     .A : Set

这是一个重要的步骤—— Agda 发现了 `x` 和 `y` 必须相等，才能与模式 `refl` 相匹配。
{::comment}
This is the key step---Agda has worked out that `x` and `y` must be
the same to match the pattern `refl`!
{:/}

最后，我们回到洞里，使用 `C-c C-r`，Agda 将会把洞变成一个可以满足给定类型的构造器实例。
{::comment}
Finally, if we go back into the hole and type `C-c C-r` it will
instantiate the hole with the one constructor that yields a value of
the expected type:
{:/}

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = refl

我们至此完成了与之前给出证明相同的证明。
{::comment}
This completes the definition as given above.
{:/}

传递性亦是很直接：
{::comment}
Transitivity is equally straightforward:
{:/}
<pre class="Agda">{% raw %}<a id="trans"></a><a id="5200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5200" class="Function">trans</a> <a id="5206" class="Symbol">:</a> <a id="5208" class="Symbol">∀</a> <a id="5210" class="Symbol">{</a><a id="5211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5211" class="Bound">A</a> <a id="5213" class="Symbol">:</a> <a id="5215" class="PrimitiveType">Set</a><a id="5218" class="Symbol">}</a> <a id="5220" class="Symbol">{</a><a id="5221" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5221" class="Bound">x</a> <a id="5223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5223" class="Bound">y</a> <a id="5225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5225" class="Bound">z</a> <a id="5227" class="Symbol">:</a> <a id="5229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5211" class="Bound">A</a><a id="5230" class="Symbol">}</a>
  <a id="5234" class="Symbol">→</a> <a id="5236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5221" class="Bound">x</a> <a id="5238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="5240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5223" class="Bound">y</a>
  <a id="5244" class="Symbol">→</a> <a id="5246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5223" class="Bound">y</a> <a id="5248" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="5250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5225" class="Bound">z</a>
    <a id="5256" class="Comment">-----</a>
  <a id="5264" class="Symbol">→</a> <a id="5266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5221" class="Bound">x</a> <a id="5268" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="5270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5225" class="Bound">z</a>
<a id="5272" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5200" class="Function">trans</a> <a id="5278" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a> <a id="5283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a>  <a id="5289" class="Symbol">=</a>  <a id="5292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a>{% endraw %}</pre>
同样，交互式地证明这个特性是一个很好的练习，尤其是观察 Agda 的已知内容根据参数的实例而变化的过程。
{::comment}
Again, a useful exercise is to carry out an interactive development,
checking how Agda's knowledge changes as each of the two arguments is
instantiated.
{:/}

## 同余性和替换性 {#cong}
{::comment}
## Congruence and substitution {#cong}
{:/}

相等性满足 *同余性*（Congurence）。如果两个项相等，那么对它们使用相同的函数，
其结果仍然相等：
{::comment}
Equality satisfies _congruence_.  If two terms are equal,
they remain so after the same function is applied to both:
{:/}
<pre class="Agda">{% raw %}<a id="cong"></a><a id="5810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5810" class="Function">cong</a> <a id="5815" class="Symbol">:</a> <a id="5817" class="Symbol">∀</a> <a id="5819" class="Symbol">{</a><a id="5820" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5820" class="Bound">A</a> <a id="5822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5822" class="Bound">B</a> <a id="5824" class="Symbol">:</a> <a id="5826" class="PrimitiveType">Set</a><a id="5829" class="Symbol">}</a> <a id="5831" class="Symbol">(</a><a id="5832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5832" class="Bound">f</a> <a id="5834" class="Symbol">:</a> <a id="5836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5820" class="Bound">A</a> <a id="5838" class="Symbol">→</a> <a id="5840" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5822" class="Bound">B</a><a id="5841" class="Symbol">)</a> <a id="5843" class="Symbol">{</a><a id="5844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5844" class="Bound">x</a> <a id="5846" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5846" class="Bound">y</a> <a id="5848" class="Symbol">:</a> <a id="5850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5820" class="Bound">A</a><a id="5851" class="Symbol">}</a>
  <a id="5855" class="Symbol">→</a> <a id="5857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5844" class="Bound">x</a> <a id="5859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="5861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5846" class="Bound">y</a>
    <a id="5867" class="Comment">---------</a>
  <a id="5879" class="Symbol">→</a> <a id="5881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5832" class="Bound">f</a> <a id="5883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5844" class="Bound">x</a> <a id="5885" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="5887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5832" class="Bound">f</a> <a id="5889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5846" class="Bound">y</a>
<a id="5891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5810" class="Function">cong</a> <a id="5896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5896" class="Bound">f</a> <a id="5898" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a>  <a id="5904" class="Symbol">=</a>  <a id="5907" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a>{% endraw %}</pre>

两个参数的函数也满足同余性：
{::comment}
Congruence of functions with two arguments is similar:
{:/}
<pre class="Agda">{% raw %}<a id="cong₂"></a><a id="6024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6024" class="Function">cong₂</a> <a id="6030" class="Symbol">:</a> <a id="6032" class="Symbol">∀</a> <a id="6034" class="Symbol">{</a><a id="6035" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6035" class="Bound">A</a> <a id="6037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6037" class="Bound">B</a> <a id="6039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6039" class="Bound">C</a> <a id="6041" class="Symbol">:</a> <a id="6043" class="PrimitiveType">Set</a><a id="6046" class="Symbol">}</a> <a id="6048" class="Symbol">(</a><a id="6049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6049" class="Bound">f</a> <a id="6051" class="Symbol">:</a> <a id="6053" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6035" class="Bound">A</a> <a id="6055" class="Symbol">→</a> <a id="6057" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6037" class="Bound">B</a> <a id="6059" class="Symbol">→</a> <a id="6061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6039" class="Bound">C</a><a id="6062" class="Symbol">)</a> <a id="6064" class="Symbol">{</a><a id="6065" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6065" class="Bound">u</a> <a id="6067" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6067" class="Bound">x</a> <a id="6069" class="Symbol">:</a> <a id="6071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6035" class="Bound">A</a><a id="6072" class="Symbol">}</a> <a id="6074" class="Symbol">{</a><a id="6075" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6075" class="Bound">v</a> <a id="6077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6077" class="Bound">y</a> <a id="6079" class="Symbol">:</a> <a id="6081" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6037" class="Bound">B</a><a id="6082" class="Symbol">}</a>
  <a id="6086" class="Symbol">→</a> <a id="6088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6065" class="Bound">u</a> <a id="6090" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="6092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6067" class="Bound">x</a>
  <a id="6096" class="Symbol">→</a> <a id="6098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6075" class="Bound">v</a> <a id="6100" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="6102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6077" class="Bound">y</a>
    <a id="6108" class="Comment">-------------</a>
  <a id="6124" class="Symbol">→</a> <a id="6126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6049" class="Bound">f</a> <a id="6128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6065" class="Bound">u</a> <a id="6130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6075" class="Bound">v</a> <a id="6132" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="6134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6049" class="Bound">f</a> <a id="6136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6067" class="Bound">x</a> <a id="6138" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6077" class="Bound">y</a>
<a id="6140" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6024" class="Function">cong₂</a> <a id="6146" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6146" class="Bound">f</a> <a id="6148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a> <a id="6153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a>  <a id="6159" class="Symbol">=</a>  <a id="6162" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a>{% endraw %}</pre>

在函数上的等价性也满足同余性。如果两个函数是相等的，那么它们作用在同一项上的结果是相等的：
{::comment}
Equality is also a congruence in the function position of an application.
If two functions are equal, then applying them to the same term
yields equal terms:
{:/}
<pre class="Agda">{% raw %}<a id="cong-app"></a><a id="6413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6413" class="Function">cong-app</a> <a id="6422" class="Symbol">:</a> <a id="6424" class="Symbol">∀</a> <a id="6426" class="Symbol">{</a><a id="6427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6427" class="Bound">A</a> <a id="6429" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6429" class="Bound">B</a> <a id="6431" class="Symbol">:</a> <a id="6433" class="PrimitiveType">Set</a><a id="6436" class="Symbol">}</a> <a id="6438" class="Symbol">{</a><a id="6439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6439" class="Bound">f</a> <a id="6441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6441" class="Bound">g</a> <a id="6443" class="Symbol">:</a> <a id="6445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6427" class="Bound">A</a> <a id="6447" class="Symbol">→</a> <a id="6449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6429" class="Bound">B</a><a id="6450" class="Symbol">}</a>
  <a id="6454" class="Symbol">→</a> <a id="6456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6439" class="Bound">f</a> <a id="6458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="6460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6441" class="Bound">g</a>
    <a id="6466" class="Comment">---------------------</a>
  <a id="6490" class="Symbol">→</a> <a id="6492" class="Symbol">∀</a> <a id="6494" class="Symbol">(</a><a id="6495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6495" class="Bound">x</a> <a id="6497" class="Symbol">:</a> <a id="6499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6427" class="Bound">A</a><a id="6500" class="Symbol">)</a> <a id="6502" class="Symbol">→</a> <a id="6504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6439" class="Bound">f</a> <a id="6506" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6495" class="Bound">x</a> <a id="6508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="6510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6441" class="Bound">g</a> <a id="6512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6495" class="Bound">x</a>
<a id="6514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6413" class="Function">cong-app</a> <a id="6523" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a> <a id="6528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6528" class="Bound">x</a> <a id="6530" class="Symbol">=</a> <a id="6532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a>{% endraw %}</pre>

相等性也满足*替换性*（Substitution）。
如果两个值相等，其中一个满足某谓词，那么另一个也满足此谓词。
{::comment}
Equality also satisfies *substitution*.
If two values are equal and a predicate holds of the first then it also holds of the second:
{:/}
<pre class="Agda">{% raw %}<a id="subst"></a><a id="6770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6770" class="Function">subst</a> <a id="6776" class="Symbol">:</a> <a id="6778" class="Symbol">∀</a> <a id="6780" class="Symbol">{</a><a id="6781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6781" class="Bound">A</a> <a id="6783" class="Symbol">:</a> <a id="6785" class="PrimitiveType">Set</a><a id="6788" class="Symbol">}</a> <a id="6790" class="Symbol">{</a><a id="6791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6791" class="Bound">x</a> <a id="6793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6793" class="Bound">y</a> <a id="6795" class="Symbol">:</a> <a id="6797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6781" class="Bound">A</a><a id="6798" class="Symbol">}</a> <a id="6800" class="Symbol">(</a><a id="6801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6801" class="Bound">P</a> <a id="6803" class="Symbol">:</a> <a id="6805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6781" class="Bound">A</a> <a id="6807" class="Symbol">→</a> <a id="6809" class="PrimitiveType">Set</a><a id="6812" class="Symbol">)</a>
  <a id="6816" class="Symbol">→</a> <a id="6818" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6791" class="Bound">x</a> <a id="6820" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="6822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6793" class="Bound">y</a>
    <a id="6828" class="Comment">---------</a>
  <a id="6840" class="Symbol">→</a> <a id="6842" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6801" class="Bound">P</a> <a id="6844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6791" class="Bound">x</a> <a id="6846" class="Symbol">→</a> <a id="6848" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6801" class="Bound">P</a> <a id="6850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6793" class="Bound">y</a>
<a id="6852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6770" class="Function">subst</a> <a id="6858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6858" class="Bound">P</a> <a id="6860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a> <a id="6865" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6865" class="Bound">px</a> <a id="6868" class="Symbol">=</a> <a id="6870" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6865" class="Bound">px</a>{% endraw %}</pre>

## 等式串
{::comment}
## Chains of equations
{:/}

我们在此演示如何使用等式串来论证，正如本书中使用证明形式。我们讲声明放在一个叫做
`≡-Reasoning` 的模块里，与 Agda 标准库中的格式相对应。
{::comment}
Here we show how to support reasoning with chains of equations, as
used throughout the book.  We package the declarations into a module,
named `≡-Reasoning`, to match the format used in Agda's standard
library:
{:/}
<pre class="Agda">{% raw %}<a id="7253" class="Keyword">module</a> <a id="≡-Reasoning"></a><a id="7260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7260" class="Module">≡-Reasoning</a> <a id="7272" class="Symbol">{</a><a id="7273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7273" class="Bound">A</a> <a id="7275" class="Symbol">:</a> <a id="7277" class="PrimitiveType">Set</a><a id="7280" class="Symbol">}</a> <a id="7282" class="Keyword">where</a>

  <a id="7291" class="Keyword">infix</a>  <a id="7298" class="Number">1</a> <a id="7300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7348" class="Function Operator">begin_</a>
  <a id="7309" class="Keyword">infixr</a> <a id="7316" class="Number">2</a> <a id="7318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7428" class="Function Operator">_≡⟨⟩_</a> <a id="7324" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7513" class="Function Operator">_≡⟨_⟩_</a>
  <a id="7333" class="Keyword">infix</a>  <a id="7340" class="Number">3</a> <a id="7342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7628" class="Function Operator">_∎</a>

  <a id="≡-Reasoning.begin_"></a><a id="7348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7348" class="Function Operator">begin_</a> <a id="7355" class="Symbol">:</a> <a id="7357" class="Symbol">∀</a> <a id="7359" class="Symbol">{</a><a id="7360" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7360" class="Bound">x</a> <a id="7362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7362" class="Bound">y</a> <a id="7364" class="Symbol">:</a> <a id="7366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7273" class="Bound">A</a><a id="7367" class="Symbol">}</a>
    <a id="7373" class="Symbol">→</a> <a id="7375" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7360" class="Bound">x</a> <a id="7377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="7379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7362" class="Bound">y</a>
      <a id="7387" class="Comment">-----</a>
    <a id="7397" class="Symbol">→</a> <a id="7399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7360" class="Bound">x</a> <a id="7401" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="7403" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7362" class="Bound">y</a>
  <a id="7407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7348" class="Function Operator">begin</a> <a id="7413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7413" class="Bound">x≡y</a>  <a id="7418" class="Symbol">=</a>  <a id="7421" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7413" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨⟩_"></a><a id="7428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7428" class="Function Operator">_≡⟨⟩_</a> <a id="7434" class="Symbol">:</a> <a id="7436" class="Symbol">∀</a> <a id="7438" class="Symbol">(</a><a id="7439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7439" class="Bound">x</a> <a id="7441" class="Symbol">:</a> <a id="7443" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7273" class="Bound">A</a><a id="7444" class="Symbol">)</a> <a id="7446" class="Symbol">{</a><a id="7447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7447" class="Bound">y</a> <a id="7449" class="Symbol">:</a> <a id="7451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7273" class="Bound">A</a><a id="7452" class="Symbol">}</a>
    <a id="7458" class="Symbol">→</a> <a id="7460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7439" class="Bound">x</a> <a id="7462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="7464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7447" class="Bound">y</a>
      <a id="7472" class="Comment">-----</a>
    <a id="7482" class="Symbol">→</a> <a id="7484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7439" class="Bound">x</a> <a id="7486" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="7488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7447" class="Bound">y</a>
  <a id="7492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7492" class="Bound">x</a> <a id="7494" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7428" class="Function Operator">≡⟨⟩</a> <a id="7498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7498" class="Bound">x≡y</a>  <a id="7503" class="Symbol">=</a>  <a id="7506" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7498" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨_⟩_"></a><a id="7513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7513" class="Function Operator">_≡⟨_⟩_</a> <a id="7520" class="Symbol">:</a> <a id="7522" class="Symbol">∀</a> <a id="7524" class="Symbol">(</a><a id="7525" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7525" class="Bound">x</a> <a id="7527" class="Symbol">:</a> <a id="7529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7273" class="Bound">A</a><a id="7530" class="Symbol">)</a> <a id="7532" class="Symbol">{</a><a id="7533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7533" class="Bound">y</a> <a id="7535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7535" class="Bound">z</a> <a id="7537" class="Symbol">:</a> <a id="7539" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7273" class="Bound">A</a><a id="7540" class="Symbol">}</a>
    <a id="7546" class="Symbol">→</a> <a id="7548" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7525" class="Bound">x</a> <a id="7550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="7552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7533" class="Bound">y</a>
    <a id="7558" class="Symbol">→</a> <a id="7560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7533" class="Bound">y</a> <a id="7562" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="7564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7535" class="Bound">z</a>
      <a id="7572" class="Comment">-----</a>
    <a id="7582" class="Symbol">→</a> <a id="7584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7525" class="Bound">x</a> <a id="7586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="7588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7535" class="Bound">z</a>
  <a id="7592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7592" class="Bound">x</a> <a id="7594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7513" class="Function Operator">≡⟨</a> <a id="7597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7597" class="Bound">x≡y</a> <a id="7601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7513" class="Function Operator">⟩</a> <a id="7603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7603" class="Bound">y≡z</a>  <a id="7608" class="Symbol">=</a>  <a id="7611" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5200" class="Function">trans</a> <a id="7617" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7597" class="Bound">x≡y</a> <a id="7621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7603" class="Bound">y≡z</a>

  <a id="≡-Reasoning._∎"></a><a id="7628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7628" class="Function Operator">_∎</a> <a id="7631" class="Symbol">:</a> <a id="7633" class="Symbol">∀</a> <a id="7635" class="Symbol">(</a><a id="7636" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7636" class="Bound">x</a> <a id="7638" class="Symbol">:</a> <a id="7640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7273" class="Bound">A</a><a id="7641" class="Symbol">)</a>
      <a id="7649" class="Comment">-----</a>
    <a id="7659" class="Symbol">→</a> <a id="7661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7636" class="Bound">x</a> <a id="7663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="7665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7636" class="Bound">x</a>
  <a id="7669" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7669" class="Bound">x</a> <a id="7671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7628" class="Function Operator">∎</a>  <a id="7674" class="Symbol">=</a>  <a id="7677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a>

<a id="7683" class="Keyword">open</a> <a id="7688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7260" class="Module">≡-Reasoning</a>{% endraw %}</pre>
这是我们第一次使用嵌套的模块。它包括了关键字 `module` 和后续的模块名、隐式或显式参数，
关键字 `where`，和模块中的内容（在缩进内）。模块里可以包括任何形式的声明，也可以包括其他模块。
嵌套的模块和本书每章节所定义的顶层模块相似，只是顶层模块不需要缩进。
打开（Open）一个模块会把模块内的所有定义导入进当前的环境中。

{::comment}
This is our first use of a nested module. It consists of the keyword
`module` followed by the module name and any parameters, explicit or
implicit, the keyword `where`, and the contents of the module indented.
Modules may contain any sort of declaration, including other nested modules.
Nested modules are similar to the top-level modules that constitute
each chapter of this book, save that the body of a top-level module
need not be indented.  Opening the module makes all of the definitions
available in the current environment.
{:/}

举个例子，我们来看看如何用等式串证明传递性：
{::comment}
As an example, let's look at a proof of transitivity
as a chain of equations:
{:/}
<pre class="Agda">{% raw %}<a id="trans′"></a><a id="8562" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8562" class="Function">trans′</a> <a id="8569" class="Symbol">:</a> <a id="8571" class="Symbol">∀</a> <a id="8573" class="Symbol">{</a><a id="8574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8574" class="Bound">A</a> <a id="8576" class="Symbol">:</a> <a id="8578" class="PrimitiveType">Set</a><a id="8581" class="Symbol">}</a> <a id="8583" class="Symbol">{</a><a id="8584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8584" class="Bound">x</a> <a id="8586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8586" class="Bound">y</a> <a id="8588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8588" class="Bound">z</a> <a id="8590" class="Symbol">:</a> <a id="8592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8574" class="Bound">A</a><a id="8593" class="Symbol">}</a>
  <a id="8597" class="Symbol">→</a> <a id="8599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8584" class="Bound">x</a> <a id="8601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="8603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8586" class="Bound">y</a>
  <a id="8607" class="Symbol">→</a> <a id="8609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8586" class="Bound">y</a> <a id="8611" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="8613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8588" class="Bound">z</a>
    <a id="8619" class="Comment">-----</a>
  <a id="8627" class="Symbol">→</a> <a id="8629" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8584" class="Bound">x</a> <a id="8631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="8633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8588" class="Bound">z</a>
<a id="8635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8562" class="Function">trans′</a> <a id="8642" class="Symbol">{</a><a id="8643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8643" class="Bound">A</a><a id="8644" class="Symbol">}</a> <a id="8646" class="Symbol">{</a><a id="8647" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8647" class="Bound">x</a><a id="8648" class="Symbol">}</a> <a id="8650" class="Symbol">{</a><a id="8651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8651" class="Bound">y</a><a id="8652" class="Symbol">}</a> <a id="8654" class="Symbol">{</a><a id="8655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8655" class="Bound">z</a><a id="8656" class="Symbol">}</a> <a id="8658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8658" class="Bound">x≡y</a> <a id="8662" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8662" class="Bound">y≡z</a> <a id="8666" class="Symbol">=</a>
  <a id="8670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7348" class="Function Operator">begin</a>
    <a id="8680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8647" class="Bound">x</a>
  <a id="8684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7513" class="Function Operator">≡⟨</a> <a id="8687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8658" class="Bound">x≡y</a> <a id="8691" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7513" class="Function Operator">⟩</a>
    <a id="8697" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8651" class="Bound">y</a>
  <a id="8701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7513" class="Function Operator">≡⟨</a> <a id="8704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8662" class="Bound">y≡z</a> <a id="8708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7513" class="Function Operator">⟩</a>
    <a id="8714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8655" class="Bound">z</a>
  <a id="8718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7628" class="Function Operator">∎</a>{% endraw %}</pre>
根据其定义，等式右边会被解析成如下：
{::comment}
According to the fixity declarations, the body parses as follows:
{:/}

    begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))

这里 `begin` 的使用纯粹是装饰性的，因为它直接返回了其参数。其参数包括了
`_≡⟨_⟩_` 作用于 `x`、`x≡y` 和 `y ≡⟨ y≡z ⟩ (z ∎)`。第一个参数是一个项 `x`，
而第二、第三个参数分别是等式 `x ≡ y`、`y ≡ z` 的证明，它们在 `_≡⟨_⟩_` 的定义中用
`trans` 连接起来，形成 `x ≡ z` 的证明。`y ≡ z` 的证明包括了 `_≡⟨_⟩_` 作用于 `y`、
`y≡z` 和 `z ∎`。第一个参数是一个项 `y`，而第二、第三个参数分别是等式 `y ≡ z`、`z ≡ z` 的证明，
它们在 `_≡⟨_⟩_` 的定义中用 `trans` 连接起来，形成 `y ≡ z` 的证明。最后，`z ≡ z`
的证明包括了 `_∎` 作用于 `z` 之上，使用了 `refl`。经过化简，上述定义等同于：
{::comment}
The application of `begin` is purely cosmetic, as it simply returns
its argument.  That argument consists of `_≡⟨_⟩_` applied to `x`,
`x≡y`, and `y ≡⟨ y≡z ⟩ (z ∎)`.  The first argument is a term, `x`,
while the second and third arguments are both proofs of equations, in
particular proofs of `x ≡ y` and `y ≡ z` respectively, which are
combined by `trans` in the body of `_≡⟨_⟩_` to yield a proof of `x ≡
z`.  The proof of `y ≡ z` consists of `_≡⟨_⟩_` applied to `y`, `y≡z`,
and `z ∎`.  The first argument is a term, `y`, while the second and
third arguments are both proofs of equations, in particular proofs of
`y ≡ z` and `z ≡ z` respectively, which are combined by `trans` in the
body of `_≡⟨_⟩_` to yield a proof of `y ≡ z`.  Finally, the proof of
`z ≡ z` consists of `_∎` applied to the term `z`, which yields `refl`.
After simplification, the body is equivalent to the term:
{:/}

    trans x≡y (trans y≡z refl)

我们可以把任意等式串转化成一系列的 `trans` 的使用。这样的证明更加精简，但是更难以阅读。
`∎` 的小窍门意味着等式串化简成为的一系列 `trans` 会以 `trans e refl` 结尾，尽管只需要 `e`
就足够了，这里的 `e` 是等式的证明。
{::comment}
We could replace any use of a chain of equations by a chain of
applications of `trans`; the result would be more compact but harder
to read.  The trick behind `∎` means that a chain of equalities
simplifies to a chain of applications of `trans` than ends in `trans e
refl`, where `e` is a term that proves some equality, even though `e`
alone would do.
{:/}

## 等式串的另外一个例子
{::comment}
## Chains of equations, another example
{:/}

我们重新证明加法的交换律来作为等式串的第二个例子。我们首先重复自然数和加法的定义。
我们不能导入它们（正如本章节开头中所解释的那样），因为那样会产生一个冲突：
{::comment}
As a second example of chains of equations, we repeat the proof that addition
is commutative.  We first repeat the definitions of naturals and addition.
We cannot import them because (as noted at the beginning of this chapter)
it would cause a conflict:
{:/}
<pre class="Agda">{% raw %}<a id="11133" class="Keyword">data</a> <a id="ℕ"></a><a id="11138" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11138" class="Datatype">ℕ</a> <a id="11140" class="Symbol">:</a> <a id="11142" class="PrimitiveType">Set</a> <a id="11146" class="Keyword">where</a>
  <a id="ℕ.zero"></a><a id="11154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11154" class="InductiveConstructor">zero</a> <a id="11159" class="Symbol">:</a> <a id="11161" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11138" class="Datatype">ℕ</a>
  <a id="ℕ.suc"></a><a id="11165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11165" class="InductiveConstructor">suc</a>  <a id="11170" class="Symbol">:</a> <a id="11172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11138" class="Datatype">ℕ</a> <a id="11174" class="Symbol">→</a> <a id="11176" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11138" class="Datatype">ℕ</a>

<a id="_+_"></a><a id="11179" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">_+_</a> <a id="11183" class="Symbol">:</a> <a id="11185" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11138" class="Datatype">ℕ</a> <a id="11187" class="Symbol">→</a> <a id="11189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11138" class="Datatype">ℕ</a> <a id="11191" class="Symbol">→</a> <a id="11193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11138" class="Datatype">ℕ</a>
<a id="11195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11154" class="InductiveConstructor">zero</a>    <a id="11203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="11205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11205" class="Bound">n</a>  <a id="11208" class="Symbol">=</a>  <a id="11211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11205" class="Bound">n</a>
<a id="11213" class="Symbol">(</a><a id="11214" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11165" class="InductiveConstructor">suc</a> <a id="11218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11218" class="Bound">m</a><a id="11219" class="Symbol">)</a> <a id="11221" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="11223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11223" class="Bound">n</a>  <a id="11226" class="Symbol">=</a>  <a id="11229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11165" class="InductiveConstructor">suc</a> <a id="11233" class="Symbol">(</a><a id="11234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11218" class="Bound">m</a> <a id="11236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="11238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11223" class="Bound">n</a><a id="11239" class="Symbol">)</a>{% endraw %}</pre>

为了节约空间，我们假设两条引理（而不是证明它们）：
{::comment}
To save space we postulate (rather than prove in full) two lemmas:
{:/}
<pre class="Agda">{% raw %}<a id="11376" class="Keyword">postulate</a>
  <a id="+-identity"></a><a id="11388" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11388" class="Postulate">+-identity</a> <a id="11399" class="Symbol">:</a> <a id="11401" class="Symbol">∀</a> <a id="11403" class="Symbol">(</a><a id="11404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11404" class="Bound">m</a> <a id="11406" class="Symbol">:</a> <a id="11408" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11138" class="Datatype">ℕ</a><a id="11409" class="Symbol">)</a> <a id="11411" class="Symbol">→</a> <a id="11413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11404" class="Bound">m</a> <a id="11415" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="11417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11154" class="InductiveConstructor">zero</a> <a id="11422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="11424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11404" class="Bound">m</a>
  <a id="+-suc"></a><a id="11428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11428" class="Postulate">+-suc</a> <a id="11434" class="Symbol">:</a> <a id="11436" class="Symbol">∀</a> <a id="11438" class="Symbol">(</a><a id="11439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11439" class="Bound">m</a> <a id="11441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11441" class="Bound">n</a> <a id="11443" class="Symbol">:</a> <a id="11445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11138" class="Datatype">ℕ</a><a id="11446" class="Symbol">)</a> <a id="11448" class="Symbol">→</a> <a id="11450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11439" class="Bound">m</a> <a id="11452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="11454" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11165" class="InductiveConstructor">suc</a> <a id="11458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11441" class="Bound">n</a> <a id="11460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="11462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11165" class="InductiveConstructor">suc</a> <a id="11466" class="Symbol">(</a><a id="11467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11439" class="Bound">m</a> <a id="11469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="11471" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11441" class="Bound">n</a><a id="11472" class="Symbol">)</a>{% endraw %}</pre>
这是我们第一次使用*假设*（Postulate）。假设为一个标识符指定一个签名，但是不提供定义。
我们在这里假设之前证明过的东西，来节约空间。假设在使用时必须加以注意。如果假设的内容为假，
那么我们可以证明出任何东西。
{::comment}
This is our first use of a _postulate_.  A postulate specifies a
signature for an identifier but no definition.  Here we postulate
something proved earlier to save space.  Postulates must be used with
caution.  If we postulate something false then we could use Agda to
prove anything whatsoever.
{:/}

我们接下来重复交换律的证明：
{::comment}
We then repeat the proof of commutativity:
{:/}
<pre class="Agda">{% raw %}<a id="+-comm"></a><a id="11997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11997" class="Function">+-comm</a> <a id="12004" class="Symbol">:</a> <a id="12006" class="Symbol">∀</a> <a id="12008" class="Symbol">(</a><a id="12009" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12009" class="Bound">m</a> <a id="12011" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12011" class="Bound">n</a> <a id="12013" class="Symbol">:</a> <a id="12015" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11138" class="Datatype">ℕ</a><a id="12016" class="Symbol">)</a> <a id="12018" class="Symbol">→</a> <a id="12020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12009" class="Bound">m</a> <a id="12022" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="12024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12011" class="Bound">n</a> <a id="12026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="12028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12011" class="Bound">n</a> <a id="12030" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="12032" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12009" class="Bound">m</a>
<a id="12034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11997" class="Function">+-comm</a> <a id="12041" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12041" class="Bound">m</a> <a id="12043" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11154" class="InductiveConstructor">zero</a> <a id="12048" class="Symbol">=</a>
  <a id="12052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7348" class="Function Operator">begin</a>
    <a id="12062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12041" class="Bound">m</a> <a id="12064" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="12066" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11154" class="InductiveConstructor">zero</a>
  <a id="12073" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7513" class="Function Operator">≡⟨</a> <a id="12076" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11388" class="Postulate">+-identity</a> <a id="12087" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12041" class="Bound">m</a> <a id="12089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7513" class="Function Operator">⟩</a>
    <a id="12095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12041" class="Bound">m</a>
  <a id="12099" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7428" class="Function Operator">≡⟨⟩</a>
    <a id="12107" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11154" class="InductiveConstructor">zero</a> <a id="12112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="12114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12041" class="Bound">m</a>
  <a id="12118" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7628" class="Function Operator">∎</a>
<a id="12120" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11997" class="Function">+-comm</a> <a id="12127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12127" class="Bound">m</a> <a id="12129" class="Symbol">(</a><a id="12130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11165" class="InductiveConstructor">suc</a> <a id="12134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12134" class="Bound">n</a><a id="12135" class="Symbol">)</a> <a id="12137" class="Symbol">=</a>
  <a id="12141" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7348" class="Function Operator">begin</a>
    <a id="12151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12127" class="Bound">m</a> <a id="12153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="12155" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11165" class="InductiveConstructor">suc</a> <a id="12159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12134" class="Bound">n</a>
  <a id="12163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7513" class="Function Operator">≡⟨</a> <a id="12166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11428" class="Postulate">+-suc</a> <a id="12172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12127" class="Bound">m</a> <a id="12174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12134" class="Bound">n</a> <a id="12176" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7513" class="Function Operator">⟩</a>
    <a id="12182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11165" class="InductiveConstructor">suc</a> <a id="12186" class="Symbol">(</a><a id="12187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12127" class="Bound">m</a> <a id="12189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="12191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12134" class="Bound">n</a><a id="12192" class="Symbol">)</a>
  <a id="12196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7513" class="Function Operator">≡⟨</a> <a id="12199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5810" class="Function">cong</a> <a id="12204" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11165" class="InductiveConstructor">suc</a> <a id="12208" class="Symbol">(</a><a id="12209" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11997" class="Function">+-comm</a> <a id="12216" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12127" class="Bound">m</a> <a id="12218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12134" class="Bound">n</a><a id="12219" class="Symbol">)</a> <a id="12221" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7513" class="Function Operator">⟩</a>
    <a id="12227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11165" class="InductiveConstructor">suc</a> <a id="12231" class="Symbol">(</a><a id="12232" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12134" class="Bound">n</a> <a id="12234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="12236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12127" class="Bound">m</a><a id="12237" class="Symbol">)</a>
  <a id="12241" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7428" class="Function Operator">≡⟨⟩</a>
    <a id="12249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11165" class="InductiveConstructor">suc</a> <a id="12253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12134" class="Bound">n</a> <a id="12255" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="12257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12127" class="Bound">m</a>
  <a id="12261" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7628" class="Function Operator">∎</a>{% endraw %}</pre>
论证的过程和之前的相似。我们在不需要解释的地方使用 `_≡⟨⟩_`，我们可以认为
`_≡⟨⟩_` 和 `_≡⟨ refl ⟩_` 是等价的。
{::comment}
The reasoning here is similar to that in the
preceding section.  We use
`_≡⟨⟩_` when no justification is required.
One can think of `_≡⟨⟩_` as equivalent to `_≡⟨ refl ⟩_`.
{:/}

Agda 总是认为一个项与其化简的项是等价的。我们之所以可以写出
{::comment}
Agda always treats a term as equivalent to its
simplified term.  The reason that one can write
{:/}

      suc (n + m)
    ≡⟨⟩
      suc n + m

是因为 Agda 认为它们是一样的。这也意味着我们可以交换两行的顺序，写出
{::comment}
is because Agda treats both terms as the same.
This also means that one could instead interchange
the lines and write
{:/}

      suc n + m
    ≡⟨⟩
      suc (n + m)

而 Agda 并不会反对。Agda 只会检查由 `≡⟨⟩` 隔开的项是否化简后相同。
而书写的顺序合不合理则是由我们自行决定。
{::comment}
and Agda would not object. Agda only checks that the terms separated
by `≡⟨⟩` have the same simplified form; it's up to us to write them in
an order that will make sense to the reader.
{:/}


#### 练习 `≤-reasoning` (延伸)
{::comment}
#### Exercise `≤-reasoning` (stretch)
{:/}

[Relations]({{ site.baseurl }}{% link out/plfa/Relations.md%}) 章节中的单调性证明亦可以用相似于 `≡-reasoning` 的，更易于理解的形式给出。
相似地来定义 `≤-reasoning`，并用其重新给出加法对于不等式是单调的证明。重写 `+-monoˡ-≤` 和 `+-mono-≤`。
{::comment}
The proof of monotonicity from
Chapter [Relations]({{ site.baseurl }}{% link out/plfa/Relations.md%})
can be written in a more readable form by using an analogue of our
notation for `≡-reasoning`.  Define `≤-reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite both `+-monoˡ-≤` and `+-mono-≤`.
{:/}

<pre class="Agda">{% raw %}<a id="13805" class="Comment">-- 在此处书写你的代码</a>{% endraw %}</pre>


## 重写
{::comment}
## Rewriting
{:/}

考虑一个自然数的性质，比如说一个数是偶数。我们重复之前给出的定义：
{::comment}
Consider a property of natural numbers, such as being even.
We repeat the earlier definition:
{:/}
<pre class="Agda">{% raw %}<a id="14026" class="Keyword">data</a> <a id="even"></a><a id="14031" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14031" class="Datatype">even</a> <a id="14036" class="Symbol">:</a> <a id="14038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11138" class="Datatype">ℕ</a> <a id="14040" class="Symbol">→</a> <a id="14042" class="PrimitiveType">Set</a>
<a id="14046" class="Keyword">data</a> <a id="odd"></a><a id="14051" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14051" class="Datatype">odd</a>  <a id="14056" class="Symbol">:</a> <a id="14058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11138" class="Datatype">ℕ</a> <a id="14060" class="Symbol">→</a> <a id="14062" class="PrimitiveType">Set</a>

<a id="14067" class="Keyword">data</a> <a id="14072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14031" class="Datatype">even</a> <a id="14077" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="14086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14086" class="InductiveConstructor">even-zero</a> <a id="14096" class="Symbol">:</a> <a id="14098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14031" class="Datatype">even</a> <a id="14103" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11154" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="14111" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14111" class="InductiveConstructor">even-suc</a> <a id="14120" class="Symbol">:</a> <a id="14122" class="Symbol">∀</a> <a id="14124" class="Symbol">{</a><a id="14125" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14125" class="Bound">n</a> <a id="14127" class="Symbol">:</a> <a id="14129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11138" class="Datatype">ℕ</a><a id="14130" class="Symbol">}</a>
    <a id="14136" class="Symbol">→</a> <a id="14138" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14051" class="Datatype">odd</a> <a id="14142" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14125" class="Bound">n</a>
      <a id="14150" class="Comment">------------</a>
    <a id="14167" class="Symbol">→</a> <a id="14169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14031" class="Datatype">even</a> <a id="14174" class="Symbol">(</a><a id="14175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11165" class="InductiveConstructor">suc</a> <a id="14179" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14125" class="Bound">n</a><a id="14180" class="Symbol">)</a>

<a id="14183" class="Keyword">data</a> <a id="14188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14051" class="Datatype">odd</a> <a id="14192" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="14200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14200" class="InductiveConstructor">odd-suc</a> <a id="14208" class="Symbol">:</a> <a id="14210" class="Symbol">∀</a> <a id="14212" class="Symbol">{</a><a id="14213" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14213" class="Bound">n</a> <a id="14215" class="Symbol">:</a> <a id="14217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11138" class="Datatype">ℕ</a><a id="14218" class="Symbol">}</a>
    <a id="14224" class="Symbol">→</a> <a id="14226" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14031" class="Datatype">even</a> <a id="14231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14213" class="Bound">n</a>
      <a id="14239" class="Comment">-----------</a>
    <a id="14255" class="Symbol">→</a> <a id="14257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14051" class="Datatype">odd</a> <a id="14261" class="Symbol">(</a><a id="14262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11165" class="InductiveConstructor">suc</a> <a id="14266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14213" class="Bound">n</a><a id="14267" class="Symbol">)</a>{% endraw %}</pre>
在前面的部分中，我们证明了加法满足交换律。给定 `even (m + n)` 成立的证据，我们应当可以用它来做
`even (n + m)` 成立的证据。
{::comment}
In the previous section, we proved addition is commutative.  Given
evidence that `even (m + n)` holds, we ought also to be able to take
that as evidence that `even (n + m)` holds.
{:/}

Agda 对这种论证有特殊记法的支持——我们之前提到过的 `rewrite` 记法。来启用这种记法，
我们只用编译程序指令来告诉 Agda 什么类型对应相等性：
{::comment}
Agda includes special notation to support just this kind of reasoning,
the `rewrite` notation we encountered earlier.
To enable this notation, we use pragmas to tell Agda which type
corresponds to equality:
{:/}
<pre class="Agda">{% raw %}<a id="14874" class="Symbol">{-#</a> <a id="14878" class="Keyword">BUILTIN</a> EQUALITY <a id="14895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">_≡_</a> <a id="14899" class="Symbol">#-}</a>{% endraw %}</pre>

我们然后就可以如下证明求证的性质：
{::comment}
We can then prove the desired property as follows:
{:/}
<pre class="Agda">{% raw %}<a id="even-comm"></a><a id="15014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15014" class="Function">even-comm</a> <a id="15024" class="Symbol">:</a> <a id="15026" class="Symbol">∀</a> <a id="15028" class="Symbol">(</a><a id="15029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15029" class="Bound">m</a> <a id="15031" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15031" class="Bound">n</a> <a id="15033" class="Symbol">:</a> <a id="15035" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11138" class="Datatype">ℕ</a><a id="15036" class="Symbol">)</a>
  <a id="15040" class="Symbol">→</a> <a id="15042" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14031" class="Datatype">even</a> <a id="15047" class="Symbol">(</a><a id="15048" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15029" class="Bound">m</a> <a id="15050" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="15052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15031" class="Bound">n</a><a id="15053" class="Symbol">)</a>
    <a id="15059" class="Comment">------------</a>
  <a id="15074" class="Symbol">→</a> <a id="15076" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14031" class="Datatype">even</a> <a id="15081" class="Symbol">(</a><a id="15082" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15031" class="Bound">n</a> <a id="15084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="15086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15029" class="Bound">m</a><a id="15087" class="Symbol">)</a>
<a id="15089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15014" class="Function">even-comm</a> <a id="15099" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15099" class="Bound">m</a> <a id="15101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15101" class="Bound">n</a> <a id="15103" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15103" class="Bound">ev</a>  <a id="15107" class="Keyword">rewrite</a> <a id="15115" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11997" class="Function">+-comm</a> <a id="15122" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15101" class="Bound">n</a> <a id="15124" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15099" class="Bound">m</a>  <a id="15127" class="Symbol">=</a>  <a id="15130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15103" class="Bound">ev</a>{% endraw %}</pre>

在这里，`ev` 包括了所有 `even (m + n)` 成立的证据，我们证明它亦可作为 `even (n + m)`
成立的证据。一般来说，关键字 `rewrite` 之后跟着一个等式的证明，这个等式被用于重写目标和任意作用域内变量的类型。

{::comment}
Here `ev` ranges over evidence that `even (m + n)` holds, and we show
that it also provides evidence that `even (n + m)` holds.  In
general, the keyword `rewrite` is followed by evidence of an
equality, and that equality is used to rewrite the type of the
goal and of any variable in scope.
{:/}

交互性地证明 `even-comm` 是很有帮助的。一开始，我们先给左边的参数赋予变量，给右手边放上一个洞：
{::comment}
It is instructive to develop `even-comm` interactively.  To start, we
supply variables for the arguments on the left, and a hole for the
body on the right:
{:/}

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev = {! !}

如果我们进入洞里，输入 `C-c C-,`，Agda 会报告：
{::comment}
If we go into the hole and type `C-c C-,` then Agda reports:
{:/}

    Goal: even (n + m)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

现在我们加入重写：
{::comment}
Now we add the rewrite:
{:/}

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev rewrite +-comm n m = {! !}

如果我们再次进入洞里，并输入 `C-c C-,`，Agda 现在会报告：
{::comment}
If we go into the hole again and type `C-c C-,` then Agda now reports:
{:/}

    Goal: even (m + n)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

目标里的参数被交换了。现在 `ev` 显然满足目标条件，输入 `C-c C-a` 会用 `ev` 来填充这个洞。
命令 `C-c C-a` 可以进行自动搜索，检查作用域内的变量是否和目标有相同的类型。
{::comment}
The arguments have been swapped in the goal.  Now it is trivial to see
that `ev` satisfies the goal, and typing `C-c C-a` in the hole causes
it to be filled with `ev`.  The command `C-c C-a` performs an
automated search, including checking whether a variable in scope has
the same type as the goal.
{:/}

## 多重重写
{::comment}
## Multiple rewrites
{:/}

我们可以多次使用重写，以竖线隔开。举个例子，这里是加法交换律的第二个证明，使用重写而不是等式串：
{::comment}
One may perform multiple rewrites, each separated by a vertical bar.  For instance,
here is a second proof that addition is commutative, relying on rewrites rather
than chains of equalities:
{:/}
<pre class="Agda">{% raw %}<a id="+-comm′"></a><a id="17358" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17358" class="Function">+-comm′</a> <a id="17366" class="Symbol">:</a> <a id="17368" class="Symbol">∀</a> <a id="17370" class="Symbol">(</a><a id="17371" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17371" class="Bound">m</a> <a id="17373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17373" class="Bound">n</a> <a id="17375" class="Symbol">:</a> <a id="17377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11138" class="Datatype">ℕ</a><a id="17378" class="Symbol">)</a> <a id="17380" class="Symbol">→</a> <a id="17382" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17371" class="Bound">m</a> <a id="17384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="17386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17373" class="Bound">n</a> <a id="17388" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="17390" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17373" class="Bound">n</a> <a id="17392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="17394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17371" class="Bound">m</a>
<a id="17396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17358" class="Function">+-comm′</a> <a id="17404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11154" class="InductiveConstructor">zero</a>    <a id="17412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17412" class="Bound">n</a>  <a id="17415" class="Keyword">rewrite</a> <a id="17423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11388" class="Postulate">+-identity</a> <a id="17434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17412" class="Bound">n</a>             <a id="17448" class="Symbol">=</a>  <a id="17451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a>
<a id="17456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17358" class="Function">+-comm′</a> <a id="17464" class="Symbol">(</a><a id="17465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11165" class="InductiveConstructor">suc</a> <a id="17469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17469" class="Bound">m</a><a id="17470" class="Symbol">)</a> <a id="17472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17472" class="Bound">n</a>  <a id="17475" class="Keyword">rewrite</a> <a id="17483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11428" class="Postulate">+-suc</a> <a id="17489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17472" class="Bound">n</a> <a id="17491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17469" class="Bound">m</a> <a id="17493" class="Symbol">|</a> <a id="17495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17358" class="Function">+-comm′</a> <a id="17503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17469" class="Bound">m</a> <a id="17505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17472" class="Bound">n</a>  <a id="17508" class="Symbol">=</a>  <a id="17511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a>{% endraw %}</pre>
这个证明更加的简短。之前的证明用 `cong suc (+-comm m n)` 作为使用归纳假设的说明，
而这里我们使用 `+-comm m n` 来重写就足够了，因为重写可以将同余性考虑在其中。尽管使用重写的证明更加的简短，
使用等式串的证明能容易理解，我们将尽可能的使用后者。
{::comment}
This is far more compact.  Among other things, whereas the previous
proof required `cong suc (+-comm m n)` as the justification to invoke
the inductive hypothesis, here it is sufficient to rewrite with
`+-comm m n`, as rewriting automatically takes congruence into
account.  Although proofs with rewriting are shorter, proofs as chains
of equalities are easier to follow, and we will stick with the latter
when feasible.
{:/}

## 深入重写
{::comment}
## Rewriting expanded
{:/}

`rewrite` 记法实际上是 `with` 抽象的一种应用：
{::comment}
The `rewrite` notation is in fact shorthand for an appropriate use of `with`
abstraction:
{:/}
<pre class="Agda">{% raw %}<a id="even-comm′"></a><a id="18309" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18309" class="Function">even-comm′</a> <a id="18320" class="Symbol">:</a> <a id="18322" class="Symbol">∀</a> <a id="18324" class="Symbol">(</a><a id="18325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18325" class="Bound">m</a> <a id="18327" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18327" class="Bound">n</a> <a id="18329" class="Symbol">:</a> <a id="18331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11138" class="Datatype">ℕ</a><a id="18332" class="Symbol">)</a>
  <a id="18336" class="Symbol">→</a> <a id="18338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14031" class="Datatype">even</a> <a id="18343" class="Symbol">(</a><a id="18344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18325" class="Bound">m</a> <a id="18346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="18348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18327" class="Bound">n</a><a id="18349" class="Symbol">)</a>
    <a id="18355" class="Comment">------------</a>
  <a id="18370" class="Symbol">→</a> <a id="18372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14031" class="Datatype">even</a> <a id="18377" class="Symbol">(</a><a id="18378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18327" class="Bound">n</a> <a id="18380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="18382" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18325" class="Bound">m</a><a id="18383" class="Symbol">)</a>
<a id="18385" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18309" class="Function">even-comm′</a> <a id="18396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18396" class="Bound">m</a> <a id="18398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18398" class="Bound">n</a> <a id="18400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18400" class="Bound">ev</a> <a id="18403" class="Keyword">with</a>   <a id="18410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18396" class="Bound">m</a> <a id="18412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="18414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18398" class="Bound">n</a>  <a id="18417" class="Symbol">|</a> <a id="18419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11997" class="Function">+-comm</a> <a id="18426" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18396" class="Bound">m</a> <a id="18428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18398" class="Bound">n</a>
<a id="18430" class="Symbol">...</a>                  <a id="18451" class="Symbol">|</a> <a id="18453" class="DottedPattern Symbol">.(</a><a id="18455" class="DottedPattern Bound">n</a> <a id="18457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="DottedPattern Function Operator">+</a> <a id="18459" class="DottedPattern Bound">m</a><a id="18460" class="DottedPattern Symbol">)</a> <a id="18462" class="Symbol">|</a> <a id="18464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a>       <a id="18475" class="Symbol">=</a> <a id="18477" class="Bound">ev</a>{% endraw %}</pre>
总的来着，我们可以在 `with` 后面跟上任何数量的表达式，用竖线分隔开，并且在每个等式中使用相同个数的模式。
我们经常将表达式和模式如上对齐。这个第一列表明了 `m + n` 和 `n + m` 是相同的，第二列使用相应等式来证明的前述的断言。
注意在这里使用的*点模式*（Dot Pattern），`.(n + m)`。点模式由一个点和一个表达式组成，
在其他信息迫使这个值和点模式中的值相等时使用。在这里，`m + n` 和 `n + m` 由后续的
`+-comm m n` 与 `refl` 的匹配来识别。我们可能会认为第一种情况是多余的，因为第二种情况中才蕴含了需要的信息。
但实际上 Agda 在这件事上很挑剔——省略第一条或者更换顺序会让 Agda 报告一个错误。（试一试你就知道！）
{::comment}
In general, one can follow `with` by any number of expressions,
separated by bars, where each following equation has the same number
of patterns.  We often write expressions and the corresponding
patterns so they line up in columns, as above. Here the first column
asserts that `m + n` and `n + m` are identical, and the second column
justifies that assertion with evidence of the appropriate equality.
Note also the use of the _dot pattern_, `.(n + m)`.  A dot pattern
consists of a dot followed by an expression, and is used when other
information forces the value matched to be equal to the value of the
expression in the dot pattern.  In this case, the identification of
`m + n` and `n + m` is justified by the subsequent matching of
`+-comm m n` against `refl`.  One might think that the first clause is
redundant as the information is inherent in the second clause, but in
fact Agda is rather picky on this point: omitting the first clause or
reversing the order of the clauses will cause Agda to report an error.
(Try it and see!)
{:/}

在这种情况中，我们也可以使用之前定义的替换函数来避免使用重写：
{::comment}
In this case, we can avoid rewrite by simply applying the substitution
function defined earlier:
{:/}
<pre class="Agda">{% raw %}<a id="even-comm″"></a><a id="20058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20058" class="Function">even-comm″</a> <a id="20069" class="Symbol">:</a> <a id="20071" class="Symbol">∀</a> <a id="20073" class="Symbol">(</a><a id="20074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20074" class="Bound">m</a> <a id="20076" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20076" class="Bound">n</a> <a id="20078" class="Symbol">:</a> <a id="20080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11138" class="Datatype">ℕ</a><a id="20081" class="Symbol">)</a>
  <a id="20085" class="Symbol">→</a> <a id="20087" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14031" class="Datatype">even</a> <a id="20092" class="Symbol">(</a><a id="20093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20074" class="Bound">m</a> <a id="20095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="20097" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20076" class="Bound">n</a><a id="20098" class="Symbol">)</a>
    <a id="20104" class="Comment">------------</a>
  <a id="20119" class="Symbol">→</a> <a id="20121" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14031" class="Datatype">even</a> <a id="20126" class="Symbol">(</a><a id="20127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20076" class="Bound">n</a> <a id="20129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11179" class="Function Operator">+</a> <a id="20131" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20074" class="Bound">m</a><a id="20132" class="Symbol">)</a>
<a id="20134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20058" class="Function">even-comm″</a> <a id="20145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20145" class="Bound">m</a> <a id="20147" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20147" class="Bound">n</a>  <a id="20150" class="Symbol">=</a>  <a id="20153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6770" class="Function">subst</a> <a id="20159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14031" class="Datatype">even</a> <a id="20164" class="Symbol">(</a><a id="20165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11997" class="Function">+-comm</a> <a id="20172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20145" class="Bound">m</a> <a id="20174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20147" class="Bound">n</a><a id="20175" class="Symbol">)</a>{% endraw %}</pre>
尽管如此，重写是 Agda 工具箱中很重要的一部分。我们会偶尔使用它，但是它有的时候是必要的。
{::comment}
Nonetheless, rewrite is a vital part of the Agda toolkit.  We will use
it sparingly, but it is occasionally essential.
{:/}

## 莱布尼兹（Leibniz）相等性
{::comment}
## Leibniz equality
{:/}

我们使用的相等性断言的形式源于 Martin Löf，于 1975 年发表。一个更早的形式源于莱布尼兹，
于 1686 年发表。莱布尼兹断言的相等性表示*不可分辨的实体*（Identity of Indiscernibles）：
两个对象相等当且仅当它们满足完全相同的性质。这条原理有时被称作莱布尼兹定律（Leibniz' Law），
与史波克定律紧密相关：“一个不造成区别的区别不是区别”。我们在这里定义莱布尼兹相等性，
并证明两个项满足莱布尼兹相等性当且仅当其满足 Martin Löf 相等性。
{::comment}
The form of asserting equality that we have used is due to Martin
Löf, and was published in 1975.  An older form is due to Leibniz, and
was published in 1686.  Leibniz asserted the _identity of
indiscernibles_: two objects are equal if and only if they satisfy the
same properties. This principle sometimes goes by the name Leibniz'
Law, and is closely related to Spock's Law, "A difference that makes
no difference is no difference".  Here we define Leibniz equality,
and show that two terms satisfy Leibniz equality if and only if they
satisfy Martin Löf equality.
{:/}

莱布尼兹不等式一般如下来定义：`x ≐ y` 当每个对于 `x` 成立的性质 `P` 对于 `y` 也成立时成立。
可能这有些出乎意料，但是这个定义亦足够保证其相反的命题：每个对于 `y` 成立的性质 `P` 对于 `x` 也成立。
{::comment}
Leibniz equality is usually formalised to state that `x ≐ y` holds if
every property `P` that holds of `x` also holds of `y`.  Perhaps
surprisingly, this definition is sufficient to also ensure the
converse, that every property `P` that holds of `y` also holds of `x`.
{:/}

令 `x` 和 `y` 为类型 `A` 的对象。我们定义 `x ≐ y` 成立，当每个对于类型 `A` 成立的谓词 `P`，
我们有 `P x` 蕴含了 `P y`：
{::comment}
Let `x` and `y` be objects of type `A`. We say that `x ≐ y` holds if
for every predicate `P` over type `A` we have that `P x` implies `P y`:
{:/}
<pre class="Agda">{% raw %}<a id="_≐_"></a><a id="21926" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21926" class="Function Operator">_≐_</a> <a id="21930" class="Symbol">:</a> <a id="21932" class="Symbol">∀</a> <a id="21934" class="Symbol">{</a><a id="21935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21935" class="Bound">A</a> <a id="21937" class="Symbol">:</a> <a id="21939" class="PrimitiveType">Set</a><a id="21942" class="Symbol">}</a> <a id="21944" class="Symbol">(</a><a id="21945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21945" class="Bound">x</a> <a id="21947" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21947" class="Bound">y</a> <a id="21949" class="Symbol">:</a> <a id="21951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21935" class="Bound">A</a><a id="21952" class="Symbol">)</a> <a id="21954" class="Symbol">→</a> <a id="21956" class="PrimitiveType">Set₁</a>
<a id="21961" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21926" class="Function Operator">_≐_</a> <a id="21965" class="Symbol">{</a><a id="21966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21966" class="Bound">A</a><a id="21967" class="Symbol">}</a> <a id="21969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21969" class="Bound">x</a> <a id="21971" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21971" class="Bound">y</a> <a id="21973" class="Symbol">=</a> <a id="21975" class="Symbol">∀</a> <a id="21977" class="Symbol">(</a><a id="21978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21978" class="Bound">P</a> <a id="21980" class="Symbol">:</a> <a id="21982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21966" class="Bound">A</a> <a id="21984" class="Symbol">→</a> <a id="21986" class="PrimitiveType">Set</a><a id="21989" class="Symbol">)</a> <a id="21991" class="Symbol">→</a> <a id="21993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21978" class="Bound">P</a> <a id="21995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21969" class="Bound">x</a> <a id="21997" class="Symbol">→</a> <a id="21999" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21978" class="Bound">P</a> <a id="22001" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21971" class="Bound">y</a>{% endraw %}</pre>
我们不能在左手边使用 `x ≐ y`，取而代之我们使用 `_≐_ {A} x y` 来提供隐式参数 `A`，这样 `A`
可以出现在右手边。
{::comment}
We cannot write the left-hand side of the equation as `x ≐ y`,
and instead we write `_≐_ {A} x y` to provide access to the implicit
parameter `A` which appears on the right-hand side.
{:/}

这是我们第一次使用*等级*（Levels）。我们不能将 `Set` 赋予类型 `Set`，因为这会导致自相矛盾，
比如罗素悖论（Russell's Paradox）或者 Girard 悖论。不同的是，我们有一个阶级的类型：其中
`Set : Set₁`，`Set₁ : Set₂`，以此类推。实际上，`Set` 本身就是 `Set₀` 的缩写。定义
`_≐_` 的等式在右手边提到了 `Set`，因此签名中必须使用 `Set₁`。我们稍后将进一步介绍等级。
{::comment}
This is our first use of _levels_.  We cannot assign `Set` the type
`Set`, since this would lead to contradictions such as Russell's
Paradox and Girard's Paradox.  Instead, there is a hierarchy of types,
where `Set : Set₁`, `Set₁ : Set₂`, and so on.  In fact, `Set` itself
is just an abbreviation for `Set₀`.  Since the equation defining `_≐_`
mentions `Set` on the right-hand side, the corresponding signature
must use `Set₁`.  We say a bit more about levels below.
{:/}

莱布尼兹相等性是自反和传递的。自反性由恒等函数的变种得来，传递性由函数组合的变种得来：
{::comment}
Leibniz equality is reflexive and transitive,
where the first follows by a variant of the identity function
and the second by a variant of function composition:
{:/}
<pre class="Agda">{% raw %}<a id="refl-≐"></a><a id="23236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23236" class="Function">refl-≐</a> <a id="23243" class="Symbol">:</a> <a id="23245" class="Symbol">∀</a> <a id="23247" class="Symbol">{</a><a id="23248" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23248" class="Bound">A</a> <a id="23250" class="Symbol">:</a> <a id="23252" class="PrimitiveType">Set</a><a id="23255" class="Symbol">}</a> <a id="23257" class="Symbol">{</a><a id="23258" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23258" class="Bound">x</a> <a id="23260" class="Symbol">:</a> <a id="23262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23248" class="Bound">A</a><a id="23263" class="Symbol">}</a>
  <a id="23267" class="Symbol">→</a> <a id="23269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23258" class="Bound">x</a> <a id="23271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21926" class="Function Operator">≐</a> <a id="23273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23258" class="Bound">x</a>
<a id="23275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23236" class="Function">refl-≐</a> <a id="23282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23282" class="Bound">P</a> <a id="23284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23284" class="Bound">Px</a>  <a id="23288" class="Symbol">=</a>  <a id="23291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23284" class="Bound">Px</a>

<a id="trans-≐"></a><a id="23295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23295" class="Function">trans-≐</a> <a id="23303" class="Symbol">:</a> <a id="23305" class="Symbol">∀</a> <a id="23307" class="Symbol">{</a><a id="23308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23308" class="Bound">A</a> <a id="23310" class="Symbol">:</a> <a id="23312" class="PrimitiveType">Set</a><a id="23315" class="Symbol">}</a> <a id="23317" class="Symbol">{</a><a id="23318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23318" class="Bound">x</a> <a id="23320" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23320" class="Bound">y</a> <a id="23322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23322" class="Bound">z</a> <a id="23324" class="Symbol">:</a> <a id="23326" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23308" class="Bound">A</a><a id="23327" class="Symbol">}</a>
  <a id="23331" class="Symbol">→</a> <a id="23333" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23318" class="Bound">x</a> <a id="23335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21926" class="Function Operator">≐</a> <a id="23337" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23320" class="Bound">y</a>
  <a id="23341" class="Symbol">→</a> <a id="23343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23320" class="Bound">y</a> <a id="23345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21926" class="Function Operator">≐</a> <a id="23347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23322" class="Bound">z</a>
    <a id="23353" class="Comment">-----</a>
  <a id="23361" class="Symbol">→</a> <a id="23363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23318" class="Bound">x</a> <a id="23365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21926" class="Function Operator">≐</a> <a id="23367" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23322" class="Bound">z</a>
<a id="23369" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23295" class="Function">trans-≐</a> <a id="23377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23377" class="Bound">x≐y</a> <a id="23381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23381" class="Bound">y≐z</a> <a id="23385" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23385" class="Bound">P</a> <a id="23387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23387" class="Bound">Px</a>  <a id="23391" class="Symbol">=</a>  <a id="23394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23381" class="Bound">y≐z</a> <a id="23398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23385" class="Bound">P</a> <a id="23400" class="Symbol">(</a><a id="23401" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23377" class="Bound">x≐y</a> <a id="23405" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23385" class="Bound">P</a> <a id="23407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23387" class="Bound">Px</a><a id="23409" class="Symbol">)</a>{% endraw %}</pre>

对称性就没有那么显然了。我们需要证明如果对于所有谓词 `P`，`P x` 蕴含 `P y`，
那么反方向的蕴含也成立。
{::comment}
Symmetry is less obvious.  We have to show that if `P x` implies `P y`
for all predicates `P`, then the implication holds the other way round
as well:
{:/}
<pre class="Agda">{% raw %}<a id="sym-≐"></a><a id="23664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23664" class="Function">sym-≐</a> <a id="23670" class="Symbol">:</a> <a id="23672" class="Symbol">∀</a> <a id="23674" class="Symbol">{</a><a id="23675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23675" class="Bound">A</a> <a id="23677" class="Symbol">:</a> <a id="23679" class="PrimitiveType">Set</a><a id="23682" class="Symbol">}</a> <a id="23684" class="Symbol">{</a><a id="23685" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23685" class="Bound">x</a> <a id="23687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23687" class="Bound">y</a> <a id="23689" class="Symbol">:</a> <a id="23691" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23675" class="Bound">A</a><a id="23692" class="Symbol">}</a>
  <a id="23696" class="Symbol">→</a> <a id="23698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23685" class="Bound">x</a> <a id="23700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21926" class="Function Operator">≐</a> <a id="23702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23687" class="Bound">y</a>
    <a id="23708" class="Comment">-----</a>
  <a id="23716" class="Symbol">→</a> <a id="23718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23687" class="Bound">y</a> <a id="23720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21926" class="Function Operator">≐</a> <a id="23722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23685" class="Bound">x</a>
<a id="23724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23664" class="Function">sym-≐</a> <a id="23730" class="Symbol">{</a><a id="23731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23731" class="Bound">A</a><a id="23732" class="Symbol">}</a> <a id="23734" class="Symbol">{</a><a id="23735" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23735" class="Bound">x</a><a id="23736" class="Symbol">}</a> <a id="23738" class="Symbol">{</a><a id="23739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23739" class="Bound">y</a><a id="23740" class="Symbol">}</a> <a id="23742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23742" class="Bound">x≐y</a> <a id="23746" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23746" class="Bound">P</a>  <a id="23749" class="Symbol">=</a>  <a id="23752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23834" class="Function">Qy</a>
  <a id="23757" class="Keyword">where</a>
    <a id="23767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23767" class="Function">Q</a> <a id="23769" class="Symbol">:</a> <a id="23771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23731" class="Bound">A</a> <a id="23773" class="Symbol">→</a> <a id="23775" class="PrimitiveType">Set</a>
    <a id="23783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23767" class="Function">Q</a> <a id="23785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23785" class="Bound">z</a> <a id="23787" class="Symbol">=</a> <a id="23789" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23746" class="Bound">P</a> <a id="23791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23785" class="Bound">z</a> <a id="23793" class="Symbol">→</a> <a id="23795" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23746" class="Bound">P</a> <a id="23797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23735" class="Bound">x</a>
    <a id="23803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23803" class="Function">Qx</a> <a id="23806" class="Symbol">:</a> <a id="23808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23767" class="Function">Q</a> <a id="23810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23735" class="Bound">x</a>
    <a id="23816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23803" class="Function">Qx</a> <a id="23819" class="Symbol">=</a> <a id="23821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23236" class="Function">refl-≐</a> <a id="23828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23746" class="Bound">P</a>
    <a id="23834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23834" class="Function">Qy</a> <a id="23837" class="Symbol">:</a> <a id="23839" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23767" class="Function">Q</a> <a id="23841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23739" class="Bound">y</a>
    <a id="23847" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23834" class="Function">Qy</a> <a id="23850" class="Symbol">=</a> <a id="23852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23742" class="Bound">x≐y</a> <a id="23856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23767" class="Function">Q</a> <a id="23858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23803" class="Function">Qx</a>{% endraw %}</pre>
给定 `x ≐ y` 、一个特定的 `P` 和一个 `P y` 的证明，我们需要构造一个 `P x` 的证明。
我们首先用一个谓词 `Q` 将相等性实例化，使得 `Q z` 在 `P z` 蕴含 `P x` 时成立。
`Q x` 这个性质是显然的，由自反性可以得出，因为 `Q y` 因为 `x ≐ y` 成立。然而 `Q y`
亦是我们需要的证明，即 `P y` 蕴含 `P x`。
{::comment}
Given `x ≐ y`, a specific `P`, and a proof of `P y`, we have to
construct a proof of `P x`.  To do so, we instantiate the equality
with a predicate `Q` such that `Q z` holds if `P z` implies `P x`.
The property `Q x` is trivial by reflexivity, and hence `Q y` follows
from `x ≐ y`.  But `Q y` is exactly a proof of what we require, that
`P y` implies `P x`.
{:/}

我们现在来证明 Martin Löf 相等性蕴含了莱布尼兹相等性，以及其逆命题。在正方向上，
如果我们已知 `x ≡ y`，我们需要对于任意的 `P`，将 `P x` 的证明转换为 `P y` 的证明。
我们很容易就可以做到这一点，因为 `x` 与 `y` 相等意味着任何 `P x` 的证明即是 `P y` 的证明。
{::comment}
We now show that Martin Löf equality implies
Leibniz equality, and vice versa.  In the forward direction, if we know
`x ≡ y` we need for any `P` to take evidence of `P x` to evidence of `P y`,
which is easy since equality of `x` and `y` implies that any proof
of `P x` is also a proof of `P y`:
{:/}
<pre class="Agda">{% raw %}<a id="≡-implies-≐"></a><a id="24926" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24926" class="Function">≡-implies-≐</a> <a id="24938" class="Symbol">:</a> <a id="24940" class="Symbol">∀</a> <a id="24942" class="Symbol">{</a><a id="24943" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24943" class="Bound">A</a> <a id="24945" class="Symbol">:</a> <a id="24947" class="PrimitiveType">Set</a><a id="24950" class="Symbol">}</a> <a id="24952" class="Symbol">{</a><a id="24953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24953" class="Bound">x</a> <a id="24955" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24955" class="Bound">y</a> <a id="24957" class="Symbol">:</a> <a id="24959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24943" class="Bound">A</a><a id="24960" class="Symbol">}</a>
  <a id="24964" class="Symbol">→</a> <a id="24966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24953" class="Bound">x</a> <a id="24968" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="24970" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24955" class="Bound">y</a>
    <a id="24976" class="Comment">-----</a>
  <a id="24984" class="Symbol">→</a> <a id="24986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24953" class="Bound">x</a> <a id="24988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21926" class="Function Operator">≐</a> <a id="24990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24955" class="Bound">y</a>
<a id="24992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24926" class="Function">≡-implies-≐</a> <a id="25004" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25004" class="Bound">x≡y</a> <a id="25008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25008" class="Bound">P</a>  <a id="25011" class="Symbol">=</a>  <a id="25014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6770" class="Function">subst</a> <a id="25020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25008" class="Bound">P</a> <a id="25022" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25004" class="Bound">x≡y</a>{% endraw %}</pre>
因为这个方向由替换性可以得来，如之前证明的那样。
{::comment}
This direction follows from substitution, which we showed earlier.
{:/}

在反方向上，我们已知对于任何 `P`，我们可以将 `P x` 的证明转换成 `P y` 的证明，
我们需要证明 `x ≡ y`：
{::comment}
In the reverse direction, given that for any `P` we can take a proof of `P x`
to a proof of `P y` we need to show `x ≡ y`:
{:/}
<pre class="Agda">{% raw %}<a id="≐-implies-≡"></a><a id="25365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25365" class="Function">≐-implies-≡</a> <a id="25377" class="Symbol">:</a> <a id="25379" class="Symbol">∀</a> <a id="25381" class="Symbol">{</a><a id="25382" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25382" class="Bound">A</a> <a id="25384" class="Symbol">:</a> <a id="25386" class="PrimitiveType">Set</a><a id="25389" class="Symbol">}</a> <a id="25391" class="Symbol">{</a><a id="25392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25392" class="Bound">x</a> <a id="25394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25394" class="Bound">y</a> <a id="25396" class="Symbol">:</a> <a id="25398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25382" class="Bound">A</a><a id="25399" class="Symbol">}</a>
  <a id="25403" class="Symbol">→</a> <a id="25405" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25392" class="Bound">x</a> <a id="25407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21926" class="Function Operator">≐</a> <a id="25409" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25394" class="Bound">y</a>
    <a id="25415" class="Comment">-----</a>
  <a id="25423" class="Symbol">→</a> <a id="25425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25392" class="Bound">x</a> <a id="25427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="25429" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25394" class="Bound">y</a>
<a id="25431" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25365" class="Function">≐-implies-≡</a> <a id="25443" class="Symbol">{</a><a id="25444" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25444" class="Bound">A</a><a id="25445" class="Symbol">}</a> <a id="25447" class="Symbol">{</a><a id="25448" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25448" class="Bound">x</a><a id="25449" class="Symbol">}</a> <a id="25451" class="Symbol">{</a><a id="25452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25452" class="Bound">y</a><a id="25453" class="Symbol">}</a> <a id="25455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25455" class="Bound">x≐y</a>  <a id="25460" class="Symbol">=</a>  <a id="25463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25537" class="Function">Qy</a>
  <a id="25468" class="Keyword">where</a>
    <a id="25478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25478" class="Function">Q</a> <a id="25480" class="Symbol">:</a> <a id="25482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25444" class="Bound">A</a> <a id="25484" class="Symbol">→</a> <a id="25486" class="PrimitiveType">Set</a>
    <a id="25494" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25478" class="Function">Q</a> <a id="25496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25496" class="Bound">z</a> <a id="25498" class="Symbol">=</a> <a id="25500" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25448" class="Bound">x</a> <a id="25502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1072" class="Datatype Operator">≡</a> <a id="25504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25496" class="Bound">z</a>
    <a id="25510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25510" class="Function">Qx</a> <a id="25513" class="Symbol">:</a> <a id="25515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25478" class="Function">Q</a> <a id="25517" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25448" class="Bound">x</a>
    <a id="25523" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25510" class="Function">Qx</a> <a id="25526" class="Symbol">=</a> <a id="25528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1112" class="InductiveConstructor">refl</a>
    <a id="25537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25537" class="Function">Qy</a> <a id="25540" class="Symbol">:</a> <a id="25542" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25478" class="Function">Q</a> <a id="25544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25452" class="Bound">y</a>
    <a id="25550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25537" class="Function">Qy</a> <a id="25553" class="Symbol">=</a> <a id="25555" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25455" class="Bound">x≐y</a> <a id="25559" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25478" class="Function">Q</a> <a id="25561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25510" class="Function">Qx</a>{% endraw %}</pre>
此证明与莱布尼兹相等性的对称性证明相似。我们取谓词 `Q`，使得 `Q z` 在 `x ≡ z` 成立时成立。
那么 `Q x` 是显然的，由 Martin Löf 相等性的自反性得来。从而 `Q y` 由 `x ≐ y` 可得，
而 `Q y` 即是我们所需要的 `x ≡ y` 的证明。
{::comment}
The proof is similar to that for symmetry of Leibniz equality. We take
`Q` to be the predicate that holds of `z` if `x ≡ z`. Then `Q x` is
trivial by reflexivity of Martin Löf equality, and hence `Q y`
follows from `x ≐ y`.  But `Q y` is exactly a proof of what we
require, that `x ≡ y`.
{:/}

（本部分的内容由此处改编得来：
*≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*
作者：Andreas Abel、Jesper Cockx、Dominique Devries、Andreas Nuyts 与 Philip Wadler，
草稿，2017）
{::comment}
(Parts of this section are adapted from *≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*, by Andreas Abel,
Jesper Cockx, Dominique Devries, Andreas Nuyts, and Philip Wadler,
draft, 2017.)
{:/}

## 全体多态 {#unipoly}
{::comment}
## Universe polymorphism {#unipoly}
{:/}

正如我们之前看到的那样，不是每个类型都属于 `Set`，但是每个类型都属于类型阶级的某处，
`Set₀`、`Set₁`、`Set₂`等等。其中 `Set` 是 `Set₀` 的缩写，此外 `Set₀ : Set₁`，`Set₁ : Set₂`，以此类推。
当我们需要比较两个属于 `Set` 的类型的值时，我们之前给出的定义是足够的，
但如果我们需要比较对于任何等级 `ℓ`，两个属于 `Set ℓ` 的类型的值该怎么办呢？
{::comment}
As we have seen, not every type belongs to `Set`, but instead every
type belongs somewhere in the hierarchy `Set₀`, `Set₁`, `Set₂`, and so on,
where `Set` abbreviates `Set₀`, and `Set₀ : Set₁`, `Set₁ : Set₂`, and so on.
The definition of equality given above is fine if we want to compare two
values of a type that belongs to `Set`, but what if we want to compare
two values of a type that belongs to `Set ℓ` for some arbitrary level `ℓ`?
{:/}

答案是*全体多态*（Universe Polymorphism），一个定义可以根据任何等级 `ℓ` 来做出。
为了使用等级，我们首先导入下列内容：
{::comment}
The answer is _universe polymorphism_, where a definition is made
with respect to an arbitrary level `ℓ`. To make use of levels, we
first import the following:
{:/}
<pre class="Agda">{% raw %}<a id="27448" class="Keyword">open</a> <a id="27453" class="Keyword">import</a> <a id="27460" href="https://agda.github.io/agda-stdlib/Level.html" class="Module">Level</a> <a id="27466" class="Keyword">using</a> <a id="27472" class="Symbol">(</a><a id="27473" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="27478" class="Symbol">;</a> <a id="27480" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#657" class="Primitive Operator">_⊔_</a><a id="27483" class="Symbol">)</a> <a id="27485" class="Keyword">renaming</a> <a id="27494" class="Symbol">(</a><a id="27495" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#611" class="Primitive">zero</a> <a id="27500" class="Symbol">to</a> <a id="27503" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#611" class="Primitive">lzero</a><a id="27508" class="Symbol">;</a> <a id="27510" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#627" class="Primitive">suc</a> <a id="27514" class="Symbol">to</a> <a id="27517" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#627" class="Primitive">lsuc</a><a id="27521" class="Symbol">)</a>{% endraw %}</pre>
我们将构造器 `zero` 和 `suc` 重命名至 `lzero` 和 `lsuc`，为了防止自然数和等级之间的混淆。
{::comment}
We rename constructors `zero` and `suc` to `lzero` and `lsuc` to avoid confusion
between levels and naturals.
{:/}

等级与自然数是同构的，有相似的构造器：
{::comment}
Levels are isomorphic to natural numbers, and have similar constructors:
{:/}

    lzero : Level
    lsuc  : Level → Level

`Set₀`、`Set₁`、`Set₂` 等名称，是下列的简写：
{::comment}
The names `Set₀`, `Set₁`, `Set₂`, and so on, are abbreviations for
{:/}

    Set lzero
    Set (lsuc lzero)
    Set (lsuc (lsuc lzero))

以此类推。我们还有一个运算符：
{::comment}
and so on. There is also an operator
{:/}

    _⊔_ : Level → Level → Level

给定两个等级，返回两者中较大的那个。
{::comment}
that given two levels returns the larger of the two.
{:/}

下面是相等性的定义，推广到任意等级：
{::comment}
Here is the definition of equality, generalised to an arbitrary level:
{:/}
<pre class="Agda">{% raw %}<a id="28375" class="Keyword">data</a> <a id="_≡′_"></a><a id="28380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28380" class="Datatype Operator">_≡′_</a> <a id="28385" class="Symbol">{</a><a id="28386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28386" class="Bound">ℓ</a> <a id="28388" class="Symbol">:</a> <a id="28390" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="28395" class="Symbol">}</a> <a id="28397" class="Symbol">{</a><a id="28398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28398" class="Bound">A</a> <a id="28400" class="Symbol">:</a> <a id="28402" class="PrimitiveType">Set</a> <a id="28406" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28386" class="Bound">ℓ</a><a id="28407" class="Symbol">}</a> <a id="28409" class="Symbol">(</a><a id="28410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28410" class="Bound">x</a> <a id="28412" class="Symbol">:</a> <a id="28414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28398" class="Bound">A</a><a id="28415" class="Symbol">)</a> <a id="28417" class="Symbol">:</a> <a id="28419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28398" class="Bound">A</a> <a id="28421" class="Symbol">→</a> <a id="28423" class="PrimitiveType">Set</a> <a id="28427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28386" class="Bound">ℓ</a> <a id="28429" class="Keyword">where</a>
  <a id="_≡′_.refl′"></a><a id="28437" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28437" class="InductiveConstructor">refl′</a> <a id="28443" class="Symbol">:</a> <a id="28445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28410" class="Bound">x</a> <a id="28447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28380" class="Datatype Operator">≡′</a> <a id="28450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28410" class="Bound">x</a>{% endraw %}</pre>
相似的，下面是对称性的推广定义：
{::comment}
Similarly, here is the generalised definition of symmetry:
{:/}
<pre class="Agda">{% raw %}<a id="sym′"></a><a id="28569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28569" class="Function">sym′</a> <a id="28574" class="Symbol">:</a> <a id="28576" class="Symbol">∀</a> <a id="28578" class="Symbol">{</a><a id="28579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28579" class="Bound">ℓ</a> <a id="28581" class="Symbol">:</a> <a id="28583" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="28588" class="Symbol">}</a> <a id="28590" class="Symbol">{</a><a id="28591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28591" class="Bound">A</a> <a id="28593" class="Symbol">:</a> <a id="28595" class="PrimitiveType">Set</a> <a id="28599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28579" class="Bound">ℓ</a><a id="28600" class="Symbol">}</a> <a id="28602" class="Symbol">{</a><a id="28603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28603" class="Bound">x</a> <a id="28605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28605" class="Bound">y</a> <a id="28607" class="Symbol">:</a> <a id="28609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28591" class="Bound">A</a><a id="28610" class="Symbol">}</a>
  <a id="28614" class="Symbol">→</a> <a id="28616" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28603" class="Bound">x</a> <a id="28618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28380" class="Datatype Operator">≡′</a> <a id="28621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28605" class="Bound">y</a>
    <a id="28627" class="Comment">------</a>
  <a id="28636" class="Symbol">→</a> <a id="28638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28605" class="Bound">y</a> <a id="28640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28380" class="Datatype Operator">≡′</a> <a id="28643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28603" class="Bound">x</a>
<a id="28645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28569" class="Function">sym′</a> <a id="28650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28437" class="InductiveConstructor">refl′</a> <a id="28656" class="Symbol">=</a> <a id="28658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28437" class="InductiveConstructor">refl′</a>{% endraw %}</pre>
为了简介，我们在本书中给出的定义将避免使用全体多态，但是大多数标准库中的定义，
包括相等性的定义，都推广到了任意等级，如上所示。
{::comment}
For simplicity, we avoid universe polymorphism in the definitions given in
the text, but most definitions in the standard library, including those for
equality, are generalised to arbitrary levels as above.
{:/}

下面是莱布尼兹相等性的推广定义：
{::comment}
Here is the generalised definition of Leibniz equality:
{:/}
<pre class="Agda">{% raw %}<a id="_≐′_"></a><a id="29068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29068" class="Function Operator">_≐′_</a> <a id="29073" class="Symbol">:</a> <a id="29075" class="Symbol">∀</a> <a id="29077" class="Symbol">{</a><a id="29078" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29078" class="Bound">ℓ</a> <a id="29080" class="Symbol">:</a> <a id="29082" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="29087" class="Symbol">}</a> <a id="29089" class="Symbol">{</a><a id="29090" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29090" class="Bound">A</a> <a id="29092" class="Symbol">:</a> <a id="29094" class="PrimitiveType">Set</a> <a id="29098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29078" class="Bound">ℓ</a><a id="29099" class="Symbol">}</a> <a id="29101" class="Symbol">(</a><a id="29102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29102" class="Bound">x</a> <a id="29104" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29104" class="Bound">y</a> <a id="29106" class="Symbol">:</a> <a id="29108" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29090" class="Bound">A</a><a id="29109" class="Symbol">)</a> <a id="29111" class="Symbol">→</a> <a id="29113" class="PrimitiveType">Set</a> <a id="29117" class="Symbol">(</a><a id="29118" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#627" class="Primitive">lsuc</a> <a id="29123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29078" class="Bound">ℓ</a><a id="29124" class="Symbol">)</a>
<a id="29126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29068" class="Function Operator">_≐′_</a> <a id="29131" class="Symbol">{</a><a id="29132" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29132" class="Bound">ℓ</a><a id="29133" class="Symbol">}</a> <a id="29135" class="Symbol">{</a><a id="29136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29136" class="Bound">A</a><a id="29137" class="Symbol">}</a> <a id="29139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29139" class="Bound">x</a> <a id="29141" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29141" class="Bound">y</a> <a id="29143" class="Symbol">=</a> <a id="29145" class="Symbol">∀</a> <a id="29147" class="Symbol">(</a><a id="29148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29148" class="Bound">P</a> <a id="29150" class="Symbol">:</a> <a id="29152" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29136" class="Bound">A</a> <a id="29154" class="Symbol">→</a> <a id="29156" class="PrimitiveType">Set</a> <a id="29160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29132" class="Bound">ℓ</a><a id="29161" class="Symbol">)</a> <a id="29163" class="Symbol">→</a> <a id="29165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29148" class="Bound">P</a> <a id="29167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29139" class="Bound">x</a> <a id="29169" class="Symbol">→</a> <a id="29171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29148" class="Bound">P</a> <a id="29173" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29141" class="Bound">y</a>{% endraw %}</pre>
之前，签名中使用了 `Set₁` 来作为一个值包括了 `Set` 的类型；而此处，我们使用
`Set (lsuc ℓ)` 来作为一个值包括了 `Set ℓ` 的类型。
{::comment}
Before the signature used `Set₁` as the type of a term that includes
`Set`, whereas here the signature uses `Set (lsuc ℓ)` as the type of a
term that includes `Set ℓ`.
{:/}

更多的关于等级的信息可以从[Agda 维基（英文）][wiki]中查询。
{::comment}
Further information on levels can be found in the [Agda Wiki][wiki].
{:/}

[wiki]: http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.UniversePolymorphism


## 标准库
{::comment}
## Standard library
{:/}

标准库中可以找到与本章节中相似的定义：
{::comment}
Definitions similar to those in this chapter can be found in the
standard library:
{:/}
<pre class="Agda">{% raw %}<a id="29854" class="Comment">-- import Relation.Binary.PropositionalEquality as Eq</a>
<a id="29908" class="Comment">-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)</a>
<a id="29972" class="Comment">-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)</a>{% endraw %}</pre>
这里的导入以注释的形式给出，以防止冲突，如引言中解释的那样。
{::comment}
Here the imports are shown as comments rather than code to avoid
collisions, as mentioned in the introduction.
{:/}


## Unicode

本章节使用下列 Unicode：
{::comment}
This chapter uses the following unicode:
{:/}

    ≡  U+2261  等同于 (\==, \equiv)
    ⟨  U+27E8  数学左尖括号 (\<)
    ⟩  U+27E9  数学右尖括号 (\>)
    ∎  U+220E  证毕 (\qed)
    ≐  U+2250  接近于极限 (\.=)
    ℓ  U+2113  手写小写 L (\ell)
    ⊔  U+2294  正方形向上开口 (\lub)
    ₀  U+2080  下标 0 (\_0)
    ₁  U+2081  下标 1 (\_1)
    ₂  U+2082  下标 2 (\_2)
