---
src       : src/plfa/Isomorphism.lagda
title     : "Isomorphism: 同构与嵌入"
layout    : page
prev      : /Equality/
permalink : /Isomorphism/
next      : /Connectives/
translators : ["Fangyi Zhou"]
progress  : 100
---

<pre class="Agda">{% raw %}<a id="194" class="Keyword">module</a> <a id="201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="218" class="Keyword">where</a>{% endraw %}</pre>

本部分介绍同构（Isomorphism）与嵌入（Embedding）。
同构可以断言两个类型是相等的，嵌入可以断言一个类型比另一个类型小。
我们会在下一章中使用同构来展示类型上的运算，例如积或者和，满足类似于交换律、结合律和分配律的性质。
{::comment}
This section introduces isomorphism as a way of asserting that two
types are equal, and embedding as a way of asserting that one type is
smaller than another.  We apply isomorphisms in the next chapter
to demonstrate that operations on types such as product and sum
satisfy properties akin to associativity, commutativity, and
distributivity.
{:/}

## 导入
{::comment}
## Imports
{:/}

<pre class="Agda">{% raw %}<a id="765" class="Keyword">import</a> <a id="772" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="810" class="Symbol">as</a> <a id="813" class="Module">Eq</a>
<a id="816" class="Keyword">open</a> <a id="821" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="824" class="Keyword">using</a> <a id="830" class="Symbol">(</a><a id="831" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="834" class="Symbol">;</a> <a id="836" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="840" class="Symbol">;</a> <a id="842" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#838" class="Function">sym</a><a id="845" class="Symbol">;</a> <a id="847" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#887" class="Function">trans</a><a id="852" class="Symbol">;</a> <a id="854" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a><a id="858" class="Symbol">;</a> <a id="860" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1274" class="Function">cong-app</a><a id="868" class="Symbol">)</a>
<a id="870" class="Keyword">open</a> <a id="875" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3975" class="Module">Eq.≡-Reasoning</a>
<a id="890" class="Keyword">open</a> <a id="895" class="Keyword">import</a> <a id="902" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="911" class="Keyword">using</a> <a id="917" class="Symbol">(</a><a id="918" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="919" class="Symbol">;</a> <a id="921" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="925" class="Symbol">;</a> <a id="927" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="930" class="Symbol">;</a> <a id="932" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="935" class="Symbol">)</a>
<a id="937" class="Keyword">open</a> <a id="942" class="Keyword">import</a> <a id="949" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="969" class="Keyword">using</a> <a id="975" class="Symbol">(</a><a id="976" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#9708" class="Function">+-comm</a><a id="982" class="Symbol">)</a>{% endraw %}</pre>


## Lambda 表达式
{::comment}
## Lambda expressions
{:/}

本章节开头将补充一些有用的基础知识：lambda 表达式，函数组合，以及外延性。
{::comment}
The chapter begins with a few preliminaries that will be useful
here and elsewhere: lambda expressions, function composition, and
extensionality.
{:/}

*Lambda 表达式*提供了一种简洁的定义函数的方法，且不需要提供函数名。一个如同这样的项：
{::comment}
_Lambda expressions_ provide a compact way to define functions without
naming them.  A term of the form
{:/}

    λ{ P₁ → N₁; ⋯ ; Pₙ → Nₙ }

等同于定义一个函数 `f`，使用下列等式：
{::comment}
is equivalent to a function `f` defined by the equations
{:/}

    f P₁ = N₁
    ⋯
    f Pₙ = Nₙ

其中 `Pₙ` 是模式（即等式的左手边），`Nₙ` 是表达式（即等式的右手边）。
{::comment}
where the `Pₙ` are patterns (left-hand sides of an equation) and the
`Nₙ` are expressions (right-hand side of an equation).
{:/}

如果只有一个等式，且模式是一个变量，我们亦可使用下面的语法：
{::comment}
In the case that there is one equation and the pattern is a variable,
we may also use the syntax
{:/}

    λ x → N

或者
{::comment}
or
{:/}

    λ (x : A) → N

两个都与 `λ{x → N}` 等价。后者可以指定函数的作用域。
{::comment}
both of which are equivalent to `λ{x → N}`. The latter allows one to
specify the domain of the function.
{:/}

往往使用匿名的 lambda 表达式比使用带名字的函数要方便：它避免了冗长的类型声明；
其定义出现在其使用的地方，所以在书写时不需要记得提前声明，在阅读时不需要上下搜索函数定义。
{::comment}
Often using an anonymous lambda expression is more convenient than
using a named function: it avoids a lengthy type declaration; and the
definition appears exactly where the function is used, so there is no
need for the writer to remember to declare it in advance, or for the
reader to search for the definition in the code.
{:/}


## 函数组合 （Function Composition）
{::comment}
## Function composition
{:/}

接下来，我们将使用函数组合：
{::comment}
In what follows, we will make use of function composition:
{:/}
<pre class="Agda">{% raw %}<a id="_∘_"></a><a id="2741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2741" class="Function Operator">_∘_</a> <a id="2745" class="Symbol">:</a> <a id="2747" class="Symbol">∀</a> <a id="2749" class="Symbol">{</a><a id="2750" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2750" class="Bound">A</a> <a id="2752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2752" class="Bound">B</a> <a id="2754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2754" class="Bound">C</a> <a id="2756" class="Symbol">:</a> <a id="2758" class="PrimitiveType">Set</a><a id="2761" class="Symbol">}</a> <a id="2763" class="Symbol">→</a> <a id="2765" class="Symbol">(</a><a id="2766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2752" class="Bound">B</a> <a id="2768" class="Symbol">→</a> <a id="2770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2754" class="Bound">C</a><a id="2771" class="Symbol">)</a> <a id="2773" class="Symbol">→</a> <a id="2775" class="Symbol">(</a><a id="2776" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2750" class="Bound">A</a> <a id="2778" class="Symbol">→</a> <a id="2780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2752" class="Bound">B</a><a id="2781" class="Symbol">)</a> <a id="2783" class="Symbol">→</a> <a id="2785" class="Symbol">(</a><a id="2786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2750" class="Bound">A</a> <a id="2788" class="Symbol">→</a> <a id="2790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2754" class="Bound">C</a><a id="2791" class="Symbol">)</a>
<a id="2793" class="Symbol">(</a><a id="2794" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2794" class="Bound">g</a> <a id="2796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2741" class="Function Operator">∘</a> <a id="2798" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2798" class="Bound">f</a><a id="2799" class="Symbol">)</a> <a id="2801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2801" class="Bound">x</a>  <a id="2804" class="Symbol">=</a> <a id="2806" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2794" class="Bound">g</a> <a id="2808" class="Symbol">(</a><a id="2809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2798" class="Bound">f</a> <a id="2811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2801" class="Bound">x</a><a id="2812" class="Symbol">)</a>{% endraw %}</pre>
`g ∘ f` 是一个函数，先使用函数 `f`，再使用函数 `g`。
一个等价的定义，使用 lambda 表达式，如下：
{::comment}
Thus, `g ∘ f` is the function that first applies `f` and
then applies `g`.  An equivalent definition, exploiting lambda
expressions, is as follows:
{:/}
<pre class="Agda">{% raw %}<a id="_∘′_"></a><a id="3064" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3064" class="Function Operator">_∘′_</a> <a id="3069" class="Symbol">:</a> <a id="3071" class="Symbol">∀</a> <a id="3073" class="Symbol">{</a><a id="3074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3074" class="Bound">A</a> <a id="3076" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3076" class="Bound">B</a> <a id="3078" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3078" class="Bound">C</a> <a id="3080" class="Symbol">:</a> <a id="3082" class="PrimitiveType">Set</a><a id="3085" class="Symbol">}</a> <a id="3087" class="Symbol">→</a> <a id="3089" class="Symbol">(</a><a id="3090" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3076" class="Bound">B</a> <a id="3092" class="Symbol">→</a> <a id="3094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3078" class="Bound">C</a><a id="3095" class="Symbol">)</a> <a id="3097" class="Symbol">→</a> <a id="3099" class="Symbol">(</a><a id="3100" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3074" class="Bound">A</a> <a id="3102" class="Symbol">→</a> <a id="3104" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3076" class="Bound">B</a><a id="3105" class="Symbol">)</a> <a id="3107" class="Symbol">→</a> <a id="3109" class="Symbol">(</a><a id="3110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3074" class="Bound">A</a> <a id="3112" class="Symbol">→</a> <a id="3114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3078" class="Bound">C</a><a id="3115" class="Symbol">)</a>
<a id="3117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3117" class="Bound">g</a> <a id="3119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3064" class="Function Operator">∘′</a> <a id="3122" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3122" class="Bound">f</a>  <a id="3125" class="Symbol">=</a>  <a id="3128" class="Symbol">λ</a> <a id="3130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3130" class="Bound">x</a> <a id="3132" class="Symbol">→</a> <a id="3134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3117" class="Bound">g</a> <a id="3136" class="Symbol">(</a><a id="3137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3122" class="Bound">f</a> <a id="3139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3130" class="Bound">x</a><a id="3140" class="Symbol">)</a>{% endraw %}</pre>


## 外延性（Extensionality） {#extensionality}
{::comment}
## Extensionality {#extensionality}
{:/}

外延性断言了区分函数的唯一方法是应用它们。如果两个函数作用在相同的参数上永远返回相同的结果，
那么两个函数相同。这是 `cong-app` 的逆命题，在[之前]({{ site.baseurl }}{% link out/plfa/Equality.md%}#cong)有所介绍。
{::comment}
Extensionality asserts that the only way to distinguish functions is
by applying them; if two functions applied to the same argument always
yield the same result, then they are the same function.  It is the
converse of `cong-app`, as introduced
[earlier]({{ site.baseurl }}{% link out/plfa/Equality.md%}#cong).
{:/}

Agda 并不预设外延性，但我们可以假设其成立：
{::comment}
Agda does not presume extensionality, but we can postulate that it holds:
{:/}
<pre class="Agda">{% raw %}<a id="3779" class="Keyword">postulate</a>
  <a id="extensionality"></a><a id="3791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3791" class="Postulate">extensionality</a> <a id="3806" class="Symbol">:</a> <a id="3808" class="Symbol">∀</a> <a id="3810" class="Symbol">{</a><a id="3811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3811" class="Bound">A</a> <a id="3813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3813" class="Bound">B</a> <a id="3815" class="Symbol">:</a> <a id="3817" class="PrimitiveType">Set</a><a id="3820" class="Symbol">}</a> <a id="3822" class="Symbol">{</a><a id="3823" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3823" class="Bound">f</a> <a id="3825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3825" class="Bound">g</a> <a id="3827" class="Symbol">:</a> <a id="3829" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3811" class="Bound">A</a> <a id="3831" class="Symbol">→</a> <a id="3833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3813" class="Bound">B</a><a id="3834" class="Symbol">}</a>
    <a id="3840" class="Symbol">→</a> <a id="3842" class="Symbol">(∀</a> <a id="3845" class="Symbol">(</a><a id="3846" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3846" class="Bound">x</a> <a id="3848" class="Symbol">:</a> <a id="3850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3811" class="Bound">A</a><a id="3851" class="Symbol">)</a> <a id="3853" class="Symbol">→</a> <a id="3855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3823" class="Bound">f</a> <a id="3857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3846" class="Bound">x</a> <a id="3859" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="3861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3825" class="Bound">g</a> <a id="3863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3846" class="Bound">x</a><a id="3864" class="Symbol">)</a>
      <a id="3872" class="Comment">-----------------------</a>
    <a id="3900" class="Symbol">→</a> <a id="3902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3823" class="Bound">f</a> <a id="3904" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="3906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3825" class="Bound">g</a>{% endraw %}</pre>
假设外延性不会造成困顿，因为我们知道它与 Agda 使用的理论是连贯一致的。
{::comment}
Postulating extensionality does not lead to difficulties, as it is
known to be consistent with the theory that underlies Agda.
{:/}

举个例子，我们考虑两个库都定义了加法，一个按照我们在 [Naturals]({{ site.baseurl }}{% link out/plfa/Naturals.md%})
章节中那样定义，另一个如下，反过来定义：
{::comment}
As an example, consider that we need results from two libraries,
one where addition is defined, as in
Chapter [Naturals]({{ site.baseurl }}{% link out/plfa/Naturals.md%}),
and one where it is defined the other way around.
{:/}
<pre class="Agda">{% raw %}<a id="_+′_"></a><a id="4394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4394" class="Function Operator">_+′_</a> <a id="4399" class="Symbol">:</a> <a id="4401" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="4403" class="Symbol">→</a> <a id="4405" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="4407" class="Symbol">→</a> <a id="4409" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a>
<a id="4411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4411" class="Bound">m</a> <a id="4413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4394" class="Function Operator">+′</a> <a id="4416" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>  <a id="4422" class="Symbol">=</a> <a id="4424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4411" class="Bound">m</a>
<a id="4426" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4426" class="Bound">m</a> <a id="4428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4394" class="Function Operator">+′</a> <a id="4431" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="4435" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4435" class="Bound">n</a> <a id="4437" class="Symbol">=</a> <a id="4439" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="4443" class="Symbol">(</a><a id="4444" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4426" class="Bound">m</a> <a id="4446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4394" class="Function Operator">+′</a> <a id="4449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4435" class="Bound">n</a><a id="4450" class="Symbol">)</a>{% endraw %}</pre>
通过使用交换律，我们可以简单地证明两个运算符在给定相同参数的情况下，
会返回相同的值：
{::comment}
Applying commutativity, it is easy to show that both operators always
return the same result given the same arguments:
{:/}
<pre class="Agda">{% raw %}<a id="same-app"></a><a id="4656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4656" class="Function">same-app</a> <a id="4665" class="Symbol">:</a> <a id="4667" class="Symbol">∀</a> <a id="4669" class="Symbol">(</a><a id="4670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4670" class="Bound">m</a> <a id="4672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4672" class="Bound">n</a> <a id="4674" class="Symbol">:</a> <a id="4676" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="4677" class="Symbol">)</a> <a id="4679" class="Symbol">→</a> <a id="4681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4670" class="Bound">m</a> <a id="4683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4394" class="Function Operator">+′</a> <a id="4686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4672" class="Bound">n</a> <a id="4688" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="4690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4670" class="Bound">m</a> <a id="4692" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="4694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4672" class="Bound">n</a>
<a id="4696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4656" class="Function">same-app</a> <a id="4705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4705" class="Bound">m</a> <a id="4707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4707" class="Bound">n</a> <a id="4709" class="Keyword">rewrite</a> <a id="4717" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#9708" class="Function">+-comm</a> <a id="4724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4705" class="Bound">m</a> <a id="4726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4707" class="Bound">n</a> <a id="4728" class="Symbol">=</a> <a id="4730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4751" class="Function">helper</a> <a id="4737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4705" class="Bound">m</a> <a id="4739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4707" class="Bound">n</a>
  <a id="4743" class="Keyword">where</a>
  <a id="4751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4751" class="Function">helper</a> <a id="4758" class="Symbol">:</a> <a id="4760" class="Symbol">∀</a> <a id="4762" class="Symbol">(</a><a id="4763" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4763" class="Bound">m</a> <a id="4765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4765" class="Bound">n</a> <a id="4767" class="Symbol">:</a> <a id="4769" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="4770" class="Symbol">)</a> <a id="4772" class="Symbol">→</a> <a id="4774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4763" class="Bound">m</a> <a id="4776" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4394" class="Function Operator">+′</a> <a id="4779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4765" class="Bound">n</a> <a id="4781" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="4783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4765" class="Bound">n</a> <a id="4785" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="4787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4763" class="Bound">m</a>
  <a id="4791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4751" class="Function">helper</a> <a id="4798" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4798" class="Bound">m</a> <a id="4800" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="4808" class="Symbol">=</a> <a id="4810" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
  <a id="4817" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4751" class="Function">helper</a> <a id="4824" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4824" class="Bound">m</a> <a id="4826" class="Symbol">(</a><a id="4827" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="4831" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4831" class="Bound">n</a><a id="4832" class="Symbol">)</a> <a id="4834" class="Symbol">=</a> <a id="4836" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="4841" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="4845" class="Symbol">(</a><a id="4846" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4751" class="Function">helper</a> <a id="4853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4824" class="Bound">m</a> <a id="4855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4831" class="Bound">n</a><a id="4856" class="Symbol">)</a>{% endraw %}</pre>

然而，有时断言两个运算符是无法区分的会更加方便。我们可以使用两次外延性：
{::comment}
However, it might be convenient to assert that the two operators are
actually indistinguishable. This we can do via two applications of
extensionality:
{:/}
<pre class="Agda">{% raw %}<a id="same"></a><a id="5089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5089" class="Function">same</a> <a id="5094" class="Symbol">:</a> <a id="5096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4394" class="Function Operator">_+′_</a> <a id="5101" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="5103" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a>
<a id="5107" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5089" class="Function">same</a> <a id="5112" class="Symbol">=</a> <a id="5114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3791" class="Postulate">extensionality</a> <a id="5129" class="Symbol">(λ</a> <a id="5132" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5132" class="Bound">m</a> <a id="5134" class="Symbol">→</a> <a id="5136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3791" class="Postulate">extensionality</a> <a id="5151" class="Symbol">(λ</a> <a id="5154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5154" class="Bound">n</a> <a id="5156" class="Symbol">→</a> <a id="5158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4656" class="Function">same-app</a> <a id="5167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5132" class="Bound">m</a> <a id="5169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5154" class="Bound">n</a><a id="5170" class="Symbol">))</a>{% endraw %}</pre>
我们偶尔需要在之后的情况中假设外延性。
{::comment}
We occasionally need to postulate extensionality in what follows.
{:/}


## 同构（Isomorphism）
{::comment}
## Isomorphism
{:/}

如果两个集合有一一对应的关系，那么它们是同构的。
下面是同构的正式定义：
{::comment}
Two sets are isomorphic if they are in one-to-one correspondence.
Here is a formal definition of isomorphism:
{:/}
<pre class="Agda">{% raw %}<a id="5518" class="Keyword">infix</a> <a id="5524" class="Number">0</a> <a id="5526" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5537" class="Record Operator">_≃_</a>
<a id="5530" class="Keyword">record</a> <a id="_≃_"></a><a id="5537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5537" class="Record Operator">_≃_</a> <a id="5541" class="Symbol">(</a><a id="5542" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5542" class="Bound">A</a> <a id="5544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5544" class="Bound">B</a> <a id="5546" class="Symbol">:</a> <a id="5548" class="PrimitiveType">Set</a><a id="5551" class="Symbol">)</a> <a id="5553" class="Symbol">:</a> <a id="5555" class="PrimitiveType">Set</a> <a id="5559" class="Keyword">where</a>
  <a id="5567" class="Keyword">field</a>
    <a id="_≃_.to"></a><a id="5577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5577" class="Field">to</a>   <a id="5582" class="Symbol">:</a> <a id="5584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5542" class="Bound">A</a> <a id="5586" class="Symbol">→</a> <a id="5588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5544" class="Bound">B</a>
    <a id="_≃_.from"></a><a id="5594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5594" class="Field">from</a> <a id="5599" class="Symbol">:</a> <a id="5601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5544" class="Bound">B</a> <a id="5603" class="Symbol">→</a> <a id="5605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5542" class="Bound">A</a>
    <a id="_≃_.from∘to"></a><a id="5611" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5611" class="Field">from∘to</a> <a id="5619" class="Symbol">:</a> <a id="5621" class="Symbol">∀</a> <a id="5623" class="Symbol">(</a><a id="5624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5624" class="Bound">x</a> <a id="5626" class="Symbol">:</a> <a id="5628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5542" class="Bound">A</a><a id="5629" class="Symbol">)</a> <a id="5631" class="Symbol">→</a> <a id="5633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5594" class="Field">from</a> <a id="5638" class="Symbol">(</a><a id="5639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5577" class="Field">to</a> <a id="5642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5624" class="Bound">x</a><a id="5643" class="Symbol">)</a> <a id="5645" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="5647" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5624" class="Bound">x</a>
    <a id="_≃_.to∘from"></a><a id="5653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5653" class="Field">to∘from</a> <a id="5661" class="Symbol">:</a> <a id="5663" class="Symbol">∀</a> <a id="5665" class="Symbol">(</a><a id="5666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5666" class="Bound">y</a> <a id="5668" class="Symbol">:</a> <a id="5670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5544" class="Bound">B</a><a id="5671" class="Symbol">)</a> <a id="5673" class="Symbol">→</a> <a id="5675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5577" class="Field">to</a> <a id="5678" class="Symbol">(</a><a id="5679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5594" class="Field">from</a> <a id="5684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5666" class="Bound">y</a><a id="5685" class="Symbol">)</a> <a id="5687" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="5689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5666" class="Bound">y</a>
<a id="5691" class="Keyword">open</a> <a id="5696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5537" class="Module Operator">_≃_</a>{% endraw %}</pre>
我们来一一展开这个定义。一个集合 `A` 和 `B` 之间的同构有四个要素：
+ 从 `A` 到 `B` 的函数 `to`
+ 从 `B` 回到 `A` 的函数 `from`
+ `from` 是 `to` 的*左逆*（left-inverse）的证明 `from∘to`
+ `from` 是 `to` 的*右逆*（right-inverse）的证明 `to∘from`

{::comment}
Let's unpack the definition. An isomorphism between sets `A` and `B` consists
of four things:
+ A function `to` from `A` to `B`,
+ A function `from` from `B` back to `A`,
+ Evidence `from∘to` asserting that `from` is a *left-inverse* for `to`,
+ Evidence `to∘from` asserting that `from` is a *right-inverse* for `to`.
{:/}

具体来说，第三条断言了 `from ∘ to` 是恒等函数，第四条断言了 `to ∘ from` 是恒等函数，
它们的名称由此得来。声明 `open _≃_` 使得 `to`、`from`、`from∘to` 和 `to∘from`
在当前作用域内可用，否则我们需要使用类似 `_≃_.to` 的写法。
{::comment}
In particular, the third asserts that `from ∘ to` is the identity, and
the fourth that `to ∘ from` is the identity, hence the names.
The declaration `open _≃_` makes available the names `to`, `from`,
`from∘to`, and `to∘from`, otherwise we would need to write `_≃_.to` and so on.
{:/}

这是我们第一次使用记录（Record）。记录声明等同于下面的归纳数据声明：
{::comment}
The above is our first use of records. A record declaration is equivalent
to a corresponding inductive data declaration:
{:/}
<pre class="Agda">{% raw %}<a id="6873" class="Keyword">data</a> <a id="_≃′_"></a><a id="6878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6878" class="Datatype Operator">_≃′_</a> <a id="6883" class="Symbol">(</a><a id="6884" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6884" class="Bound">A</a> <a id="6886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6886" class="Bound">B</a> <a id="6888" class="Symbol">:</a> <a id="6890" class="PrimitiveType">Set</a><a id="6893" class="Symbol">):</a> <a id="6896" class="PrimitiveType">Set</a> <a id="6900" class="Keyword">where</a>
  <a id="_≃′_.mk-≃′"></a><a id="6908" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6908" class="InductiveConstructor">mk-≃′</a> <a id="6914" class="Symbol">:</a> <a id="6916" class="Symbol">∀</a> <a id="6918" class="Symbol">(</a><a id="6919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6919" class="Bound">to</a> <a id="6922" class="Symbol">:</a> <a id="6924" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6884" class="Bound">A</a> <a id="6926" class="Symbol">→</a> <a id="6928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6886" class="Bound">B</a><a id="6929" class="Symbol">)</a> <a id="6931" class="Symbol">→</a>
          <a id="6943" class="Symbol">∀</a> <a id="6945" class="Symbol">(</a><a id="6946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6946" class="Bound">from</a> <a id="6951" class="Symbol">:</a> <a id="6953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6886" class="Bound">B</a> <a id="6955" class="Symbol">→</a> <a id="6957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6884" class="Bound">A</a><a id="6958" class="Symbol">)</a> <a id="6960" class="Symbol">→</a>
          <a id="6972" class="Symbol">∀</a> <a id="6974" class="Symbol">(</a><a id="6975" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6975" class="Bound">from∘to</a> <a id="6983" class="Symbol">:</a> <a id="6985" class="Symbol">(∀</a> <a id="6988" class="Symbol">(</a><a id="6989" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6989" class="Bound">x</a> <a id="6991" class="Symbol">:</a> <a id="6993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6884" class="Bound">A</a><a id="6994" class="Symbol">)</a> <a id="6996" class="Symbol">→</a> <a id="6998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6946" class="Bound">from</a> <a id="7003" class="Symbol">(</a><a id="7004" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6919" class="Bound">to</a> <a id="7007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6989" class="Bound">x</a><a id="7008" class="Symbol">)</a> <a id="7010" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="7012" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6989" class="Bound">x</a><a id="7013" class="Symbol">))</a> <a id="7016" class="Symbol">→</a>
          <a id="7028" class="Symbol">∀</a> <a id="7030" class="Symbol">(</a><a id="7031" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7031" class="Bound">to∘from</a> <a id="7039" class="Symbol">:</a> <a id="7041" class="Symbol">(∀</a> <a id="7044" class="Symbol">(</a><a id="7045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7045" class="Bound">y</a> <a id="7047" class="Symbol">:</a> <a id="7049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6886" class="Bound">B</a><a id="7050" class="Symbol">)</a> <a id="7052" class="Symbol">→</a> <a id="7054" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6919" class="Bound">to</a> <a id="7057" class="Symbol">(</a><a id="7058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6946" class="Bound">from</a> <a id="7063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7045" class="Bound">y</a><a id="7064" class="Symbol">)</a> <a id="7066" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="7068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7045" class="Bound">y</a><a id="7069" class="Symbol">))</a> <a id="7072" class="Symbol">→</a>
          <a id="7084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6884" class="Bound">A</a> <a id="7086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6878" class="Datatype Operator">≃′</a> <a id="7089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6886" class="Bound">B</a>

<a id="to′"></a><a id="7092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7092" class="Function">to′</a> <a id="7096" class="Symbol">:</a> <a id="7098" class="Symbol">∀</a> <a id="7100" class="Symbol">{</a><a id="7101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7101" class="Bound">A</a> <a id="7103" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7103" class="Bound">B</a> <a id="7105" class="Symbol">:</a> <a id="7107" class="PrimitiveType">Set</a><a id="7110" class="Symbol">}</a> <a id="7112" class="Symbol">→</a> <a id="7114" class="Symbol">(</a><a id="7115" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7101" class="Bound">A</a> <a id="7117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6878" class="Datatype Operator">≃′</a> <a id="7120" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7103" class="Bound">B</a><a id="7121" class="Symbol">)</a> <a id="7123" class="Symbol">→</a> <a id="7125" class="Symbol">(</a><a id="7126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7101" class="Bound">A</a> <a id="7128" class="Symbol">→</a> <a id="7130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7103" class="Bound">B</a><a id="7131" class="Symbol">)</a>
<a id="7133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7092" class="Function">to′</a> <a id="7137" class="Symbol">(</a><a id="7138" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6908" class="InductiveConstructor">mk-≃′</a> <a id="7144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7144" class="Bound">f</a> <a id="7146" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7146" class="Bound">g</a> <a id="7148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7148" class="Bound">g∘f</a> <a id="7152" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7152" class="Bound">f∘g</a><a id="7155" class="Symbol">)</a> <a id="7157" class="Symbol">=</a> <a id="7159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7144" class="Bound">f</a>

<a id="from′"></a><a id="7162" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7162" class="Function">from′</a> <a id="7168" class="Symbol">:</a> <a id="7170" class="Symbol">∀</a> <a id="7172" class="Symbol">{</a><a id="7173" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7173" class="Bound">A</a> <a id="7175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7175" class="Bound">B</a> <a id="7177" class="Symbol">:</a> <a id="7179" class="PrimitiveType">Set</a><a id="7182" class="Symbol">}</a> <a id="7184" class="Symbol">→</a> <a id="7186" class="Symbol">(</a><a id="7187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7173" class="Bound">A</a> <a id="7189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6878" class="Datatype Operator">≃′</a> <a id="7192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7175" class="Bound">B</a><a id="7193" class="Symbol">)</a> <a id="7195" class="Symbol">→</a> <a id="7197" class="Symbol">(</a><a id="7198" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7175" class="Bound">B</a> <a id="7200" class="Symbol">→</a> <a id="7202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7173" class="Bound">A</a><a id="7203" class="Symbol">)</a>
<a id="7205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7162" class="Function">from′</a> <a id="7211" class="Symbol">(</a><a id="7212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6908" class="InductiveConstructor">mk-≃′</a> <a id="7218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7218" class="Bound">f</a> <a id="7220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7220" class="Bound">g</a> <a id="7222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7222" class="Bound">g∘f</a> <a id="7226" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7226" class="Bound">f∘g</a><a id="7229" class="Symbol">)</a> <a id="7231" class="Symbol">=</a> <a id="7233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7220" class="Bound">g</a>

<a id="from∘to′"></a><a id="7236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7236" class="Function">from∘to′</a> <a id="7245" class="Symbol">:</a> <a id="7247" class="Symbol">∀</a> <a id="7249" class="Symbol">{</a><a id="7250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7250" class="Bound">A</a> <a id="7252" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7252" class="Bound">B</a> <a id="7254" class="Symbol">:</a> <a id="7256" class="PrimitiveType">Set</a><a id="7259" class="Symbol">}</a> <a id="7261" class="Symbol">→</a> <a id="7263" class="Symbol">(</a><a id="7264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7264" class="Bound">A≃B</a> <a id="7268" class="Symbol">:</a> <a id="7270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7250" class="Bound">A</a> <a id="7272" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6878" class="Datatype Operator">≃′</a> <a id="7275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7252" class="Bound">B</a><a id="7276" class="Symbol">)</a> <a id="7278" class="Symbol">→</a> <a id="7280" class="Symbol">(∀</a> <a id="7283" class="Symbol">(</a><a id="7284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7284" class="Bound">x</a> <a id="7286" class="Symbol">:</a> <a id="7288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7250" class="Bound">A</a><a id="7289" class="Symbol">)</a> <a id="7291" class="Symbol">→</a> <a id="7293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7162" class="Function">from′</a> <a id="7299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7264" class="Bound">A≃B</a> <a id="7303" class="Symbol">(</a><a id="7304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7092" class="Function">to′</a> <a id="7308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7264" class="Bound">A≃B</a> <a id="7312" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7284" class="Bound">x</a><a id="7313" class="Symbol">)</a> <a id="7315" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="7317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7284" class="Bound">x</a><a id="7318" class="Symbol">)</a>
<a id="7320" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7236" class="Function">from∘to′</a> <a id="7329" class="Symbol">(</a><a id="7330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6908" class="InductiveConstructor">mk-≃′</a> <a id="7336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7336" class="Bound">f</a> <a id="7338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7338" class="Bound">g</a> <a id="7340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7340" class="Bound">g∘f</a> <a id="7344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7344" class="Bound">f∘g</a><a id="7347" class="Symbol">)</a> <a id="7349" class="Symbol">=</a> <a id="7351" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7340" class="Bound">g∘f</a>

<a id="to∘from′"></a><a id="7356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7356" class="Function">to∘from′</a> <a id="7365" class="Symbol">:</a> <a id="7367" class="Symbol">∀</a> <a id="7369" class="Symbol">{</a><a id="7370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7370" class="Bound">A</a> <a id="7372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7372" class="Bound">B</a> <a id="7374" class="Symbol">:</a> <a id="7376" class="PrimitiveType">Set</a><a id="7379" class="Symbol">}</a> <a id="7381" class="Symbol">→</a> <a id="7383" class="Symbol">(</a><a id="7384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7384" class="Bound">A≃B</a> <a id="7388" class="Symbol">:</a> <a id="7390" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7370" class="Bound">A</a> <a id="7392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6878" class="Datatype Operator">≃′</a> <a id="7395" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7372" class="Bound">B</a><a id="7396" class="Symbol">)</a> <a id="7398" class="Symbol">→</a> <a id="7400" class="Symbol">(∀</a> <a id="7403" class="Symbol">(</a><a id="7404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7404" class="Bound">y</a> <a id="7406" class="Symbol">:</a> <a id="7408" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7372" class="Bound">B</a><a id="7409" class="Symbol">)</a> <a id="7411" class="Symbol">→</a> <a id="7413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7092" class="Function">to′</a> <a id="7417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7384" class="Bound">A≃B</a> <a id="7421" class="Symbol">(</a><a id="7422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7162" class="Function">from′</a> <a id="7428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7384" class="Bound">A≃B</a> <a id="7432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7404" class="Bound">y</a><a id="7433" class="Symbol">)</a> <a id="7435" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="7437" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7404" class="Bound">y</a><a id="7438" class="Symbol">)</a>
<a id="7440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7356" class="Function">to∘from′</a> <a id="7449" class="Symbol">(</a><a id="7450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6908" class="InductiveConstructor">mk-≃′</a> <a id="7456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7456" class="Bound">f</a> <a id="7458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7458" class="Bound">g</a> <a id="7460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7460" class="Bound">g∘f</a> <a id="7464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7464" class="Bound">f∘g</a><a id="7467" class="Symbol">)</a> <a id="7469" class="Symbol">=</a> <a id="7471" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7464" class="Bound">f∘g</a>{% endraw %}</pre>

我们用下面的语法来构造一个记录类型的值：
{::comment}
We construct values of the record type with the syntax
{:/}

    record
      { to    = f
      ; from  = g
      ; from∘to = g∘f
      ; to∘from = f∘g
      }

这与使用相应的归纳类型的构造器对应：
{::comment}
which corresponds to using the constructor of the corresponding
inductive type
{:/}

    mk-≃′ f g g∘f f∘g

其中 `f`、`g`、`g∘f` 和 `f∘g` 是相应类型的值。
{::comment}
where `f`, `g`, `g∘f`, and `f∘g` are values of suitable types.
{:/}


## 同构是一个等价关系
{::comment}
## Isomorphism is an equivalence
{:/}

同构是一个等价关系。这意味着它自反、对称、传递。要证明同构是自反的，我们用恒等函数作为 `to` 和 `from`：
{::comment}
Isomorphism is an equivalence, meaning that it is reflexive, symmetric,
and transitive.  To show isomorphism is reflexive, we take both `to`
and `from` to be the identity function:
{:/}
<pre class="Agda">{% raw %}<a id="≃-refl"></a><a id="8271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8271" class="Function">≃-refl</a> <a id="8278" class="Symbol">:</a> <a id="8280" class="Symbol">∀</a> <a id="8282" class="Symbol">{</a><a id="8283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8283" class="Bound">A</a> <a id="8285" class="Symbol">:</a> <a id="8287" class="PrimitiveType">Set</a><a id="8290" class="Symbol">}</a>
    <a id="8296" class="Comment">-----</a>
  <a id="8304" class="Symbol">→</a> <a id="8306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8283" class="Bound">A</a> <a id="8308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5537" class="Record Operator">≃</a> <a id="8310" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8283" class="Bound">A</a>
<a id="8312" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8271" class="Function">≃-refl</a> <a id="8319" class="Symbol">=</a>
  <a id="8323" class="Keyword">record</a>
    <a id="8334" class="Symbol">{</a> <a id="8336" class="Field">to</a>      <a id="8344" class="Symbol">=</a> <a id="8346" class="Symbol">λ{</a><a id="8348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8348" class="Bound">x</a> <a id="8350" class="Symbol">→</a> <a id="8352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8348" class="Bound">x</a><a id="8353" class="Symbol">}</a>
    <a id="8359" class="Symbol">;</a> <a id="8361" class="Field">from</a>    <a id="8369" class="Symbol">=</a> <a id="8371" class="Symbol">λ{</a><a id="8373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8373" class="Bound">y</a> <a id="8375" class="Symbol">→</a> <a id="8377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8373" class="Bound">y</a><a id="8378" class="Symbol">}</a>
    <a id="8384" class="Symbol">;</a> <a id="8386" class="Field">from∘to</a> <a id="8394" class="Symbol">=</a> <a id="8396" class="Symbol">λ{</a><a id="8398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8398" class="Bound">x</a> <a id="8400" class="Symbol">→</a> <a id="8402" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="8406" class="Symbol">}</a>
    <a id="8412" class="Symbol">;</a> <a id="8414" class="Field">to∘from</a> <a id="8422" class="Symbol">=</a> <a id="8424" class="Symbol">λ{</a><a id="8426" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8426" class="Bound">y</a> <a id="8428" class="Symbol">→</a> <a id="8430" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="8434" class="Symbol">}</a>
    <a id="8440" class="Symbol">}</a>{% endraw %}</pre>
如上，`to` 和 `from` 都是恒等函数，`from∘to` 和 `to∘from` 都是丢弃参数、返回
`refl` 的函数。在这样的情况下，`refl` 足够可以证明左逆，因为 `from (to x)`
化简为 `x`。右逆的证明同理。
{::comment}
In the above, `to` and `from` are both bound to identity functions,
and `from∘to` and `to∘from` are both bound to functions that discard
their argument and return `refl`.  In this case, `refl` alone is an
adequate proof since for the left inverse, `from (to x)`
simplifies to `x`, and similarly for the right inverse.
{:/}

要证明同构是对称的，我们把 `to` 和 `from`、`from∘to` 和 `to∘from` 互换：
{::comment}
To show isomorphism is symmetric, we simply swap the roles of `to`
and `from`, and `from∘to` and `to∘from`:
{:/}
<pre class="Agda">{% raw %}<a id="≃-sym"></a><a id="9106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9106" class="Function">≃-sym</a> <a id="9112" class="Symbol">:</a> <a id="9114" class="Symbol">∀</a> <a id="9116" class="Symbol">{</a><a id="9117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9117" class="Bound">A</a> <a id="9119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9119" class="Bound">B</a> <a id="9121" class="Symbol">:</a> <a id="9123" class="PrimitiveType">Set</a><a id="9126" class="Symbol">}</a>
  <a id="9130" class="Symbol">→</a> <a id="9132" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9117" class="Bound">A</a> <a id="9134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5537" class="Record Operator">≃</a> <a id="9136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9119" class="Bound">B</a>
    <a id="9142" class="Comment">-----</a>
  <a id="9150" class="Symbol">→</a> <a id="9152" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9119" class="Bound">B</a> <a id="9154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5537" class="Record Operator">≃</a> <a id="9156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9117" class="Bound">A</a>
<a id="9158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9106" class="Function">≃-sym</a> <a id="9164" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9164" class="Bound">A≃B</a> <a id="9168" class="Symbol">=</a>
  <a id="9172" class="Keyword">record</a>
    <a id="9183" class="Symbol">{</a> <a id="9185" class="Field">to</a>      <a id="9193" class="Symbol">=</a> <a id="9195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5594" class="Field">from</a> <a id="9200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9164" class="Bound">A≃B</a>
    <a id="9208" class="Symbol">;</a> <a id="9210" class="Field">from</a>    <a id="9218" class="Symbol">=</a> <a id="9220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5577" class="Field">to</a>   <a id="9225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9164" class="Bound">A≃B</a>
    <a id="9233" class="Symbol">;</a> <a id="9235" class="Field">from∘to</a> <a id="9243" class="Symbol">=</a> <a id="9245" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5653" class="Field">to∘from</a> <a id="9253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9164" class="Bound">A≃B</a>
    <a id="9261" class="Symbol">;</a> <a id="9263" class="Field">to∘from</a> <a id="9271" class="Symbol">=</a> <a id="9273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5611" class="Field">from∘to</a> <a id="9281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9164" class="Bound">A≃B</a>
    <a id="9289" class="Symbol">}</a>{% endraw %}</pre>

要证明同构是传递的，我们将 `to` 和 `from` 函数进行组合，并使用相等性论证来结合左逆和右逆：
{::comment}
To show isomorphism is transitive, we compose the `to` and `from`
functions, and use equational reasoning to combine the inverses:
{:/}
<pre class="Agda">{% raw %}<a id="≃-trans"></a><a id="9517" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9517" class="Function">≃-trans</a> <a id="9525" class="Symbol">:</a> <a id="9527" class="Symbol">∀</a> <a id="9529" class="Symbol">{</a><a id="9530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9530" class="Bound">A</a> <a id="9532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9532" class="Bound">B</a> <a id="9534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9534" class="Bound">C</a> <a id="9536" class="Symbol">:</a> <a id="9538" class="PrimitiveType">Set</a><a id="9541" class="Symbol">}</a>
  <a id="9545" class="Symbol">→</a> <a id="9547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9530" class="Bound">A</a> <a id="9549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5537" class="Record Operator">≃</a> <a id="9551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9532" class="Bound">B</a>
  <a id="9555" class="Symbol">→</a> <a id="9557" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9532" class="Bound">B</a> <a id="9559" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5537" class="Record Operator">≃</a> <a id="9561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9534" class="Bound">C</a>
    <a id="9567" class="Comment">-----</a>
  <a id="9575" class="Symbol">→</a> <a id="9577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9530" class="Bound">A</a> <a id="9579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5537" class="Record Operator">≃</a> <a id="9581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9534" class="Bound">C</a>
<a id="9583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9517" class="Function">≃-trans</a> <a id="9591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9591" class="Bound">A≃B</a> <a id="9595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9595" class="Bound">B≃C</a> <a id="9599" class="Symbol">=</a>
  <a id="9603" class="Keyword">record</a>
    <a id="9614" class="Symbol">{</a> <a id="9616" class="Field">to</a>       <a id="9625" class="Symbol">=</a> <a id="9627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5577" class="Field">to</a>   <a id="9632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9595" class="Bound">B≃C</a> <a id="9636" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2741" class="Function Operator">∘</a> <a id="9638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5577" class="Field">to</a>   <a id="9643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9591" class="Bound">A≃B</a>
    <a id="9651" class="Symbol">;</a> <a id="9653" class="Field">from</a>     <a id="9662" class="Symbol">=</a> <a id="9664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5594" class="Field">from</a> <a id="9669" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9591" class="Bound">A≃B</a> <a id="9673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2741" class="Function Operator">∘</a> <a id="9675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5594" class="Field">from</a> <a id="9680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9595" class="Bound">B≃C</a>
    <a id="9688" class="Symbol">;</a> <a id="9690" class="Field">from∘to</a>  <a id="9699" class="Symbol">=</a> <a id="9701" class="Symbol">λ{</a><a id="9703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9703" class="Bound">x</a> <a id="9705" class="Symbol">→</a>
        <a id="9715" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
          <a id="9731" class="Symbol">(</a><a id="9732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5594" class="Field">from</a> <a id="9737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9591" class="Bound">A≃B</a> <a id="9741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2741" class="Function Operator">∘</a> <a id="9743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5594" class="Field">from</a> <a id="9748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9595" class="Bound">B≃C</a><a id="9751" class="Symbol">)</a> <a id="9753" class="Symbol">((</a><a id="9755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5577" class="Field">to</a> <a id="9758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9595" class="Bound">B≃C</a> <a id="9762" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2741" class="Function Operator">∘</a> <a id="9764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5577" class="Field">to</a> <a id="9767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9591" class="Bound">A≃B</a><a id="9770" class="Symbol">)</a> <a id="9772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9703" class="Bound">x</a><a id="9773" class="Symbol">)</a>
        <a id="9783" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
          <a id="9797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5594" class="Field">from</a> <a id="9802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9591" class="Bound">A≃B</a> <a id="9806" class="Symbol">(</a><a id="9807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5594" class="Field">from</a> <a id="9812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9595" class="Bound">B≃C</a> <a id="9816" class="Symbol">(</a><a id="9817" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5577" class="Field">to</a> <a id="9820" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9595" class="Bound">B≃C</a> <a id="9824" class="Symbol">(</a><a id="9825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5577" class="Field">to</a> <a id="9828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9591" class="Bound">A≃B</a> <a id="9832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9703" class="Bound">x</a><a id="9833" class="Symbol">)))</a>
        <a id="9845" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="9848" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="9853" class="Symbol">(</a><a id="9854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5594" class="Field">from</a> <a id="9859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9591" class="Bound">A≃B</a><a id="9862" class="Symbol">)</a> <a id="9864" class="Symbol">(</a><a id="9865" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5611" class="Field">from∘to</a> <a id="9873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9595" class="Bound">B≃C</a> <a id="9877" class="Symbol">(</a><a id="9878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5577" class="Field">to</a> <a id="9881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9591" class="Bound">A≃B</a> <a id="9885" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9703" class="Bound">x</a><a id="9886" class="Symbol">))</a> <a id="9889" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
          <a id="9901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5594" class="Field">from</a> <a id="9906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9591" class="Bound">A≃B</a> <a id="9910" class="Symbol">(</a><a id="9911" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5577" class="Field">to</a> <a id="9914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9591" class="Bound">A≃B</a> <a id="9918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9703" class="Bound">x</a><a id="9919" class="Symbol">)</a>
        <a id="9929" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="9932" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5611" class="Field">from∘to</a> <a id="9940" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9591" class="Bound">A≃B</a> <a id="9944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9703" class="Bound">x</a> <a id="9946" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
          <a id="9958" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9703" class="Bound">x</a>
        <a id="9968" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a><a id="9969" class="Symbol">}</a>
    <a id="9975" class="Symbol">;</a> <a id="9977" class="Field">to∘from</a> <a id="9985" class="Symbol">=</a> <a id="9987" class="Symbol">λ{</a><a id="9989" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9989" class="Bound">y</a> <a id="9991" class="Symbol">→</a>
        <a id="10001" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
          <a id="10017" class="Symbol">(</a><a id="10018" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5577" class="Field">to</a> <a id="10021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9595" class="Bound">B≃C</a> <a id="10025" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2741" class="Function Operator">∘</a> <a id="10027" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5577" class="Field">to</a> <a id="10030" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9591" class="Bound">A≃B</a><a id="10033" class="Symbol">)</a> <a id="10035" class="Symbol">((</a><a id="10037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5594" class="Field">from</a> <a id="10042" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9591" class="Bound">A≃B</a> <a id="10046" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2741" class="Function Operator">∘</a> <a id="10048" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5594" class="Field">from</a> <a id="10053" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9595" class="Bound">B≃C</a><a id="10056" class="Symbol">)</a> <a id="10058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9989" class="Bound">y</a><a id="10059" class="Symbol">)</a>
        <a id="10069" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
          <a id="10083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5577" class="Field">to</a> <a id="10086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9595" class="Bound">B≃C</a> <a id="10090" class="Symbol">(</a><a id="10091" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5577" class="Field">to</a> <a id="10094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9591" class="Bound">A≃B</a> <a id="10098" class="Symbol">(</a><a id="10099" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5594" class="Field">from</a> <a id="10104" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9591" class="Bound">A≃B</a> <a id="10108" class="Symbol">(</a><a id="10109" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5594" class="Field">from</a> <a id="10114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9595" class="Bound">B≃C</a> <a id="10118" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9989" class="Bound">y</a><a id="10119" class="Symbol">)))</a>
        <a id="10131" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="10134" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="10139" class="Symbol">(</a><a id="10140" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5577" class="Field">to</a> <a id="10143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9595" class="Bound">B≃C</a><a id="10146" class="Symbol">)</a> <a id="10148" class="Symbol">(</a><a id="10149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5653" class="Field">to∘from</a> <a id="10157" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9591" class="Bound">A≃B</a> <a id="10161" class="Symbol">(</a><a id="10162" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5594" class="Field">from</a> <a id="10167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9595" class="Bound">B≃C</a> <a id="10171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9989" class="Bound">y</a><a id="10172" class="Symbol">))</a> <a id="10175" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
          <a id="10187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5577" class="Field">to</a> <a id="10190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9595" class="Bound">B≃C</a> <a id="10194" class="Symbol">(</a><a id="10195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5594" class="Field">from</a> <a id="10200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9595" class="Bound">B≃C</a> <a id="10204" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9989" class="Bound">y</a><a id="10205" class="Symbol">)</a>
        <a id="10215" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="10218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5653" class="Field">to∘from</a> <a id="10226" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9595" class="Bound">B≃C</a> <a id="10230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9989" class="Bound">y</a> <a id="10232" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
          <a id="10244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9989" class="Bound">y</a>
        <a id="10254" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a><a id="10255" class="Symbol">}</a>
     <a id="10262" class="Symbol">}</a>{% endraw %}</pre>


## 同构的相等性论证
{::comment}
## Equational reasoning for isomorphism
{:/}

我们可以直接的构造一种同构的相等性论证方法。我们对之前的相等性论证定义进行修改。
我们省略 `_≡⟨⟩_` 的定义，因为简单的同构比简单的相等性出现的少很多：
{::comment}
It is straightforward to support a variant of equational reasoning for
isomorphism.  We essentially copy the previous definition
of equality for isomorphism.  We omit the form that corresponds to `_≡⟨⟩_`, since
trivial isomorphisms arise far less often than trivial equalities:
{:/}

<pre class="Agda">{% raw %}<a id="10736" class="Keyword">module</a> <a id="≃-Reasoning"></a><a id="10743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10743" class="Module">≃-Reasoning</a> <a id="10755" class="Keyword">where</a>

  <a id="10764" class="Keyword">infix</a>  <a id="10771" class="Number">1</a> <a id="10773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10819" class="Function Operator">≃-begin_</a>
  <a id="10784" class="Keyword">infixr</a> <a id="10791" class="Number">2</a> <a id="10793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10903" class="Function Operator">_≃⟨_⟩_</a>
  <a id="10802" class="Keyword">infix</a>  <a id="10809" class="Number">3</a> <a id="10811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11022" class="Function Operator">_≃-∎</a>

  <a id="≃-Reasoning.≃-begin_"></a><a id="10819" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10819" class="Function Operator">≃-begin_</a> <a id="10828" class="Symbol">:</a> <a id="10830" class="Symbol">∀</a> <a id="10832" class="Symbol">{</a><a id="10833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10833" class="Bound">A</a> <a id="10835" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10835" class="Bound">B</a> <a id="10837" class="Symbol">:</a> <a id="10839" class="PrimitiveType">Set</a><a id="10842" class="Symbol">}</a>
    <a id="10848" class="Symbol">→</a> <a id="10850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10833" class="Bound">A</a> <a id="10852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5537" class="Record Operator">≃</a> <a id="10854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10835" class="Bound">B</a>
      <a id="10862" class="Comment">-----</a>
    <a id="10872" class="Symbol">→</a> <a id="10874" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10833" class="Bound">A</a> <a id="10876" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5537" class="Record Operator">≃</a> <a id="10878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10835" class="Bound">B</a>
  <a id="10882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10819" class="Function Operator">≃-begin</a> <a id="10890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10890" class="Bound">A≃B</a> <a id="10894" class="Symbol">=</a> <a id="10896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10890" class="Bound">A≃B</a>

  <a id="≃-Reasoning._≃⟨_⟩_"></a><a id="10903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10903" class="Function Operator">_≃⟨_⟩_</a> <a id="10910" class="Symbol">:</a> <a id="10912" class="Symbol">∀</a> <a id="10914" class="Symbol">(</a><a id="10915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10915" class="Bound">A</a> <a id="10917" class="Symbol">:</a> <a id="10919" class="PrimitiveType">Set</a><a id="10922" class="Symbol">)</a> <a id="10924" class="Symbol">{</a><a id="10925" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10925" class="Bound">B</a> <a id="10927" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10927" class="Bound">C</a> <a id="10929" class="Symbol">:</a> <a id="10931" class="PrimitiveType">Set</a><a id="10934" class="Symbol">}</a>
    <a id="10940" class="Symbol">→</a> <a id="10942" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10915" class="Bound">A</a> <a id="10944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5537" class="Record Operator">≃</a> <a id="10946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10925" class="Bound">B</a>
    <a id="10952" class="Symbol">→</a> <a id="10954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10925" class="Bound">B</a> <a id="10956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5537" class="Record Operator">≃</a> <a id="10958" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10927" class="Bound">C</a>
      <a id="10966" class="Comment">-----</a>
    <a id="10976" class="Symbol">→</a> <a id="10978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10915" class="Bound">A</a> <a id="10980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5537" class="Record Operator">≃</a> <a id="10982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10927" class="Bound">C</a>
  <a id="10986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10986" class="Bound">A</a> <a id="10988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10903" class="Function Operator">≃⟨</a> <a id="10991" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10991" class="Bound">A≃B</a> <a id="10995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10903" class="Function Operator">⟩</a> <a id="10997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10997" class="Bound">B≃C</a> <a id="11001" class="Symbol">=</a> <a id="11003" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9517" class="Function">≃-trans</a> <a id="11011" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10991" class="Bound">A≃B</a> <a id="11015" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10997" class="Bound">B≃C</a>

  <a id="≃-Reasoning._≃-∎"></a><a id="11022" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11022" class="Function Operator">_≃-∎</a> <a id="11027" class="Symbol">:</a> <a id="11029" class="Symbol">∀</a> <a id="11031" class="Symbol">(</a><a id="11032" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11032" class="Bound">A</a> <a id="11034" class="Symbol">:</a> <a id="11036" class="PrimitiveType">Set</a><a id="11039" class="Symbol">)</a>
      <a id="11047" class="Comment">-----</a>
    <a id="11057" class="Symbol">→</a> <a id="11059" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11032" class="Bound">A</a> <a id="11061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5537" class="Record Operator">≃</a> <a id="11063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11032" class="Bound">A</a>
  <a id="11067" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11067" class="Bound">A</a> <a id="11069" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11022" class="Function Operator">≃-∎</a> <a id="11073" class="Symbol">=</a> <a id="11075" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8271" class="Function">≃-refl</a>

<a id="11083" class="Keyword">open</a> <a id="11088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10743" class="Module">≃-Reasoning</a>{% endraw %}</pre>


## 嵌入（Embedding）
{::comment}
## Embedding
{:/}

我们同时也需要*嵌入*的概念，它是同构的弱化概念。同构要求证明两个类型之间的一一对应，
而嵌入只需要第一种类型涵盖在第二种类型内，所以两个类型之间有一对多的对应关系。
{::comment}
We also need the notion of _embedding_, which is a weakening of
isomorphism.  While an isomorphism shows that two types are in
one-to-one correspondence, an embedding shows that the first type is
included in the second; or, equivalently, that there is a many-to-one
correspondence between the second type and the first.
{:/}

嵌入的正式定义如下：
{::comment}
Here is the formal definition of embedding:
{:/}
<pre class="Agda">{% raw %}<a id="11668" class="Keyword">infix</a> <a id="11674" class="Number">0</a> <a id="11676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11687" class="Record Operator">_≲_</a>
<a id="11680" class="Keyword">record</a> <a id="_≲_"></a><a id="11687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11687" class="Record Operator">_≲_</a> <a id="11691" class="Symbol">(</a><a id="11692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11692" class="Bound">A</a> <a id="11694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11694" class="Bound">B</a> <a id="11696" class="Symbol">:</a> <a id="11698" class="PrimitiveType">Set</a><a id="11701" class="Symbol">)</a> <a id="11703" class="Symbol">:</a> <a id="11705" class="PrimitiveType">Set</a> <a id="11709" class="Keyword">where</a>
  <a id="11717" class="Keyword">field</a>
    <a id="_≲_.to"></a><a id="11727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11727" class="Field">to</a>      <a id="11735" class="Symbol">:</a> <a id="11737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11692" class="Bound">A</a> <a id="11739" class="Symbol">→</a> <a id="11741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11694" class="Bound">B</a>
    <a id="_≲_.from"></a><a id="11747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11747" class="Field">from</a>    <a id="11755" class="Symbol">:</a> <a id="11757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11694" class="Bound">B</a> <a id="11759" class="Symbol">→</a> <a id="11761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11692" class="Bound">A</a>
    <a id="_≲_.from∘to"></a><a id="11767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11767" class="Field">from∘to</a> <a id="11775" class="Symbol">:</a> <a id="11777" class="Symbol">∀</a> <a id="11779" class="Symbol">(</a><a id="11780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11780" class="Bound">x</a> <a id="11782" class="Symbol">:</a> <a id="11784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11692" class="Bound">A</a><a id="11785" class="Symbol">)</a> <a id="11787" class="Symbol">→</a> <a id="11789" class="Field">from</a> <a id="11794" class="Symbol">(</a><a id="11795" class="Field">to</a> <a id="11798" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11780" class="Bound">x</a><a id="11799" class="Symbol">)</a> <a id="11801" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="11803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11780" class="Bound">x</a>
<a id="11805" class="Keyword">open</a> <a id="11810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11687" class="Module Operator">_≲_</a>{% endraw %}</pre>
除了它缺少了 `to∘from` 字段以外，嵌入的定义和同构是一样的。因此，我们可以得知 `from` 是 `to`
的左逆，但是 `from` 不是 `to` 的右逆。
{::comment}
It is the same as an isomorphism, save that it lacks the `to∘from` field.
Hence, we know that `from` is left-inverse to `to`, but not that `from`
is right-inverse to `to`.
{:/}

嵌入是自反和传递的，但不是对称的。证明与同构类似，不过去除了不需要的部分：
{::comment}
Embedding is reflexive and transitive, but not symmetric.  The proofs
are cut down versions of the similar proofs for isomorphism:
{:/}
<pre class="Agda">{% raw %}<a id="≲-refl"></a><a id="12300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12300" class="Function">≲-refl</a> <a id="12307" class="Symbol">:</a> <a id="12309" class="Symbol">∀</a> <a id="12311" class="Symbol">{</a><a id="12312" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12312" class="Bound">A</a> <a id="12314" class="Symbol">:</a> <a id="12316" class="PrimitiveType">Set</a><a id="12319" class="Symbol">}</a> <a id="12321" class="Symbol">→</a> <a id="12323" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12312" class="Bound">A</a> <a id="12325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11687" class="Record Operator">≲</a> <a id="12327" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12312" class="Bound">A</a>
<a id="12329" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12300" class="Function">≲-refl</a> <a id="12336" class="Symbol">=</a>
  <a id="12340" class="Keyword">record</a>
    <a id="12351" class="Symbol">{</a> <a id="12353" class="Field">to</a>      <a id="12361" class="Symbol">=</a> <a id="12363" class="Symbol">λ{</a><a id="12365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12365" class="Bound">x</a> <a id="12367" class="Symbol">→</a> <a id="12369" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12365" class="Bound">x</a><a id="12370" class="Symbol">}</a>
    <a id="12376" class="Symbol">;</a> <a id="12378" class="Field">from</a>    <a id="12386" class="Symbol">=</a> <a id="12388" class="Symbol">λ{</a><a id="12390" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12390" class="Bound">y</a> <a id="12392" class="Symbol">→</a> <a id="12394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12390" class="Bound">y</a><a id="12395" class="Symbol">}</a>
    <a id="12401" class="Symbol">;</a> <a id="12403" class="Field">from∘to</a> <a id="12411" class="Symbol">=</a> <a id="12413" class="Symbol">λ{</a><a id="12415" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12415" class="Bound">x</a> <a id="12417" class="Symbol">→</a> <a id="12419" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="12423" class="Symbol">}</a>
    <a id="12429" class="Symbol">}</a>

<a id="≲-trans"></a><a id="12432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12432" class="Function">≲-trans</a> <a id="12440" class="Symbol">:</a> <a id="12442" class="Symbol">∀</a> <a id="12444" class="Symbol">{</a><a id="12445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12445" class="Bound">A</a> <a id="12447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12447" class="Bound">B</a> <a id="12449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12449" class="Bound">C</a> <a id="12451" class="Symbol">:</a> <a id="12453" class="PrimitiveType">Set</a><a id="12456" class="Symbol">}</a> <a id="12458" class="Symbol">→</a> <a id="12460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12445" class="Bound">A</a> <a id="12462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11687" class="Record Operator">≲</a> <a id="12464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12447" class="Bound">B</a> <a id="12466" class="Symbol">→</a> <a id="12468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12447" class="Bound">B</a> <a id="12470" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11687" class="Record Operator">≲</a> <a id="12472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12449" class="Bound">C</a> <a id="12474" class="Symbol">→</a> <a id="12476" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12445" class="Bound">A</a> <a id="12478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11687" class="Record Operator">≲</a> <a id="12480" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12449" class="Bound">C</a>
<a id="12482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12432" class="Function">≲-trans</a> <a id="12490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12490" class="Bound">A≲B</a> <a id="12494" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12494" class="Bound">B≲C</a> <a id="12498" class="Symbol">=</a>
  <a id="12502" class="Keyword">record</a>
    <a id="12513" class="Symbol">{</a> <a id="12515" class="Field">to</a>      <a id="12523" class="Symbol">=</a> <a id="12525" class="Symbol">λ{</a><a id="12527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12527" class="Bound">x</a> <a id="12529" class="Symbol">→</a> <a id="12531" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11727" class="Field">to</a>   <a id="12536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12494" class="Bound">B≲C</a> <a id="12540" class="Symbol">(</a><a id="12541" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11727" class="Field">to</a>   <a id="12546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12490" class="Bound">A≲B</a> <a id="12550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12527" class="Bound">x</a><a id="12551" class="Symbol">)}</a>
    <a id="12558" class="Symbol">;</a> <a id="12560" class="Field">from</a>    <a id="12568" class="Symbol">=</a> <a id="12570" class="Symbol">λ{</a><a id="12572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12572" class="Bound">y</a> <a id="12574" class="Symbol">→</a> <a id="12576" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11747" class="Field">from</a> <a id="12581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12490" class="Bound">A≲B</a> <a id="12585" class="Symbol">(</a><a id="12586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11747" class="Field">from</a> <a id="12591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12494" class="Bound">B≲C</a> <a id="12595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12572" class="Bound">y</a><a id="12596" class="Symbol">)}</a>
    <a id="12603" class="Symbol">;</a> <a id="12605" class="Field">from∘to</a> <a id="12613" class="Symbol">=</a> <a id="12615" class="Symbol">λ{</a><a id="12617" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12617" class="Bound">x</a> <a id="12619" class="Symbol">→</a>
        <a id="12629" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
          <a id="12645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11747" class="Field">from</a> <a id="12650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12490" class="Bound">A≲B</a> <a id="12654" class="Symbol">(</a><a id="12655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11747" class="Field">from</a> <a id="12660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12494" class="Bound">B≲C</a> <a id="12664" class="Symbol">(</a><a id="12665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11727" class="Field">to</a> <a id="12668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12494" class="Bound">B≲C</a> <a id="12672" class="Symbol">(</a><a id="12673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11727" class="Field">to</a> <a id="12676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12490" class="Bound">A≲B</a> <a id="12680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12617" class="Bound">x</a><a id="12681" class="Symbol">)))</a>
        <a id="12693" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="12696" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="12701" class="Symbol">(</a><a id="12702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11747" class="Field">from</a> <a id="12707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12490" class="Bound">A≲B</a><a id="12710" class="Symbol">)</a> <a id="12712" class="Symbol">(</a><a id="12713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11767" class="Field">from∘to</a> <a id="12721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12494" class="Bound">B≲C</a> <a id="12725" class="Symbol">(</a><a id="12726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11727" class="Field">to</a> <a id="12729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12490" class="Bound">A≲B</a> <a id="12733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12617" class="Bound">x</a><a id="12734" class="Symbol">))</a> <a id="12737" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
          <a id="12749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11747" class="Field">from</a> <a id="12754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12490" class="Bound">A≲B</a> <a id="12758" class="Symbol">(</a><a id="12759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11727" class="Field">to</a> <a id="12762" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12490" class="Bound">A≲B</a> <a id="12766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12617" class="Bound">x</a><a id="12767" class="Symbol">)</a>
        <a id="12777" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="12780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11767" class="Field">from∘to</a> <a id="12788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12490" class="Bound">A≲B</a> <a id="12792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12617" class="Bound">x</a> <a id="12794" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
          <a id="12806" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12617" class="Bound">x</a>
        <a id="12816" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a><a id="12817" class="Symbol">}</a>
     <a id="12824" class="Symbol">}</a>{% endraw %}</pre>

显而易见的是，如果两个类型相互嵌入，且其嵌入函数相互对应，那么它们是同构的。
这个一种反对称性的弱化形式：
{::comment}
It is also easy to see that if two types embed in each other, and the
embedding functions correspond, then they are isomorphic.  This is a
weak form of anti-symmetry:
{:/}
<pre class="Agda">{% raw %}<a id="≲-antisym"></a><a id="13089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13089" class="Function">≲-antisym</a> <a id="13099" class="Symbol">:</a> <a id="13101" class="Symbol">∀</a> <a id="13103" class="Symbol">{</a><a id="13104" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13104" class="Bound">A</a> <a id="13106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13106" class="Bound">B</a> <a id="13108" class="Symbol">:</a> <a id="13110" class="PrimitiveType">Set</a><a id="13113" class="Symbol">}</a>
  <a id="13117" class="Symbol">→</a> <a id="13119" class="Symbol">(</a><a id="13120" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13120" class="Bound">A≲B</a> <a id="13124" class="Symbol">:</a> <a id="13126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13104" class="Bound">A</a> <a id="13128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11687" class="Record Operator">≲</a> <a id="13130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13106" class="Bound">B</a><a id="13131" class="Symbol">)</a>
  <a id="13135" class="Symbol">→</a> <a id="13137" class="Symbol">(</a><a id="13138" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13138" class="Bound">B≲A</a> <a id="13142" class="Symbol">:</a> <a id="13144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13106" class="Bound">B</a> <a id="13146" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11687" class="Record Operator">≲</a> <a id="13148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13104" class="Bound">A</a><a id="13149" class="Symbol">)</a>
  <a id="13153" class="Symbol">→</a> <a id="13155" class="Symbol">(</a><a id="13156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11727" class="Field">to</a> <a id="13159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13120" class="Bound">A≲B</a> <a id="13163" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11747" class="Field">from</a> <a id="13170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13138" class="Bound">B≲A</a><a id="13173" class="Symbol">)</a>
  <a id="13177" class="Symbol">→</a> <a id="13179" class="Symbol">(</a><a id="13180" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11747" class="Field">from</a> <a id="13185" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13120" class="Bound">A≲B</a> <a id="13189" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11727" class="Field">to</a> <a id="13194" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13138" class="Bound">B≲A</a><a id="13197" class="Symbol">)</a>
    <a id="13203" class="Comment">-------------------</a>
  <a id="13225" class="Symbol">→</a> <a id="13227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13104" class="Bound">A</a> <a id="13229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5537" class="Record Operator">≃</a> <a id="13231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13106" class="Bound">B</a>
<a id="13233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13089" class="Function">≲-antisym</a> <a id="13243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13243" class="Bound">A≲B</a> <a id="13247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13247" class="Bound">B≲A</a> <a id="13251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13251" class="Bound">to≡from</a> <a id="13259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13259" class="Bound">from≡to</a> <a id="13267" class="Symbol">=</a>
  <a id="13271" class="Keyword">record</a>
    <a id="13282" class="Symbol">{</a> <a id="13284" class="Field">to</a>      <a id="13292" class="Symbol">=</a> <a id="13294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11727" class="Field">to</a> <a id="13297" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13243" class="Bound">A≲B</a>
    <a id="13305" class="Symbol">;</a> <a id="13307" class="Field">from</a>    <a id="13315" class="Symbol">=</a> <a id="13317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11747" class="Field">from</a> <a id="13322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13243" class="Bound">A≲B</a>
    <a id="13330" class="Symbol">;</a> <a id="13332" class="Field">from∘to</a> <a id="13340" class="Symbol">=</a> <a id="13342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11767" class="Field">from∘to</a> <a id="13350" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13243" class="Bound">A≲B</a>
    <a id="13358" class="Symbol">;</a> <a id="13360" class="Field">to∘from</a> <a id="13368" class="Symbol">=</a> <a id="13370" class="Symbol">λ{</a><a id="13372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13372" class="Bound">y</a> <a id="13374" class="Symbol">→</a>
        <a id="13384" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
          <a id="13400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11727" class="Field">to</a> <a id="13403" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13243" class="Bound">A≲B</a> <a id="13407" class="Symbol">(</a><a id="13408" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11747" class="Field">from</a> <a id="13413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13243" class="Bound">A≲B</a> <a id="13417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13372" class="Bound">y</a><a id="13418" class="Symbol">)</a>
        <a id="13428" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="13431" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="13436" class="Symbol">(</a><a id="13437" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11727" class="Field">to</a> <a id="13440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13243" class="Bound">A≲B</a><a id="13443" class="Symbol">)</a> <a id="13445" class="Symbol">(</a><a id="13446" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1274" class="Function">cong-app</a> <a id="13455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13259" class="Bound">from≡to</a> <a id="13463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13372" class="Bound">y</a><a id="13464" class="Symbol">)</a> <a id="13466" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
          <a id="13478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11727" class="Field">to</a> <a id="13481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13243" class="Bound">A≲B</a> <a id="13485" class="Symbol">(</a><a id="13486" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11727" class="Field">to</a> <a id="13489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13247" class="Bound">B≲A</a> <a id="13493" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13372" class="Bound">y</a><a id="13494" class="Symbol">)</a>
        <a id="13504" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="13507" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1274" class="Function">cong-app</a> <a id="13516" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13251" class="Bound">to≡from</a> <a id="13524" class="Symbol">(</a><a id="13525" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11727" class="Field">to</a> <a id="13528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13247" class="Bound">B≲A</a> <a id="13532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13372" class="Bound">y</a><a id="13533" class="Symbol">)</a> <a id="13535" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
          <a id="13547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11747" class="Field">from</a> <a id="13552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13247" class="Bound">B≲A</a> <a id="13556" class="Symbol">(</a><a id="13557" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11727" class="Field">to</a> <a id="13560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13247" class="Bound">B≲A</a> <a id="13564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13372" class="Bound">y</a><a id="13565" class="Symbol">)</a>
        <a id="13575" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="13578" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11767" class="Field">from∘to</a> <a id="13586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13247" class="Bound">B≲A</a> <a id="13590" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13372" class="Bound">y</a> <a id="13592" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
          <a id="13604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13372" class="Bound">y</a>
        <a id="13614" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a><a id="13615" class="Symbol">}</a>
    <a id="13621" class="Symbol">}</a>{% endraw %}</pre>
前三部分可以直接从嵌入中得来，最后一部分我们可以把 `B ≲ A` 中的左逆和两个嵌入中的 `to` 与 `from` 部分的相等性来获得同构中的右逆。
{::comment}
The first three components are copied from the embedding, while the
last combines the left inverse of `B ≲ A` with the equivalences of
the `to` and `from` components from the two embeddings to obtain
the right inverse of the isomorphism.
{:/}


## 嵌入的相等性论证
{::comment}
## Equational reasoning for embedding
{:/}

和同构类似，我们亦支持嵌入的相等性论证：
{::comment}
We can also support tabular reasoning for embedding,
analogous to that used for isomorphism:
{:/}

<pre class="Agda">{% raw %}<a id="14182" class="Keyword">module</a> <a id="≲-Reasoning"></a><a id="14189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14189" class="Module">≲-Reasoning</a> <a id="14201" class="Keyword">where</a>

  <a id="14210" class="Keyword">infix</a>  <a id="14217" class="Number">1</a> <a id="14219" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14265" class="Function Operator">≲-begin_</a>
  <a id="14230" class="Keyword">infixr</a> <a id="14237" class="Number">2</a> <a id="14239" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14349" class="Function Operator">_≲⟨_⟩_</a>
  <a id="14248" class="Keyword">infix</a>  <a id="14255" class="Number">3</a> <a id="14257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14468" class="Function Operator">_≲-∎</a>

  <a id="≲-Reasoning.≲-begin_"></a><a id="14265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14265" class="Function Operator">≲-begin_</a> <a id="14274" class="Symbol">:</a> <a id="14276" class="Symbol">∀</a> <a id="14278" class="Symbol">{</a><a id="14279" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14279" class="Bound">A</a> <a id="14281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14281" class="Bound">B</a> <a id="14283" class="Symbol">:</a> <a id="14285" class="PrimitiveType">Set</a><a id="14288" class="Symbol">}</a>
    <a id="14294" class="Symbol">→</a> <a id="14296" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14279" class="Bound">A</a> <a id="14298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11687" class="Record Operator">≲</a> <a id="14300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14281" class="Bound">B</a>
      <a id="14308" class="Comment">-----</a>
    <a id="14318" class="Symbol">→</a> <a id="14320" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14279" class="Bound">A</a> <a id="14322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11687" class="Record Operator">≲</a> <a id="14324" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14281" class="Bound">B</a>
  <a id="14328" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14265" class="Function Operator">≲-begin</a> <a id="14336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14336" class="Bound">A≲B</a> <a id="14340" class="Symbol">=</a> <a id="14342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14336" class="Bound">A≲B</a>

  <a id="≲-Reasoning._≲⟨_⟩_"></a><a id="14349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14349" class="Function Operator">_≲⟨_⟩_</a> <a id="14356" class="Symbol">:</a> <a id="14358" class="Symbol">∀</a> <a id="14360" class="Symbol">(</a><a id="14361" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14361" class="Bound">A</a> <a id="14363" class="Symbol">:</a> <a id="14365" class="PrimitiveType">Set</a><a id="14368" class="Symbol">)</a> <a id="14370" class="Symbol">{</a><a id="14371" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14371" class="Bound">B</a> <a id="14373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14373" class="Bound">C</a> <a id="14375" class="Symbol">:</a> <a id="14377" class="PrimitiveType">Set</a><a id="14380" class="Symbol">}</a>
    <a id="14386" class="Symbol">→</a> <a id="14388" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14361" class="Bound">A</a> <a id="14390" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11687" class="Record Operator">≲</a> <a id="14392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14371" class="Bound">B</a>
    <a id="14398" class="Symbol">→</a> <a id="14400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14371" class="Bound">B</a> <a id="14402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11687" class="Record Operator">≲</a> <a id="14404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14373" class="Bound">C</a>
      <a id="14412" class="Comment">-----</a>
    <a id="14422" class="Symbol">→</a> <a id="14424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14361" class="Bound">A</a> <a id="14426" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11687" class="Record Operator">≲</a> <a id="14428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14373" class="Bound">C</a>
  <a id="14432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14432" class="Bound">A</a> <a id="14434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14349" class="Function Operator">≲⟨</a> <a id="14437" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14437" class="Bound">A≲B</a> <a id="14441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14349" class="Function Operator">⟩</a> <a id="14443" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14443" class="Bound">B≲C</a> <a id="14447" class="Symbol">=</a> <a id="14449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12432" class="Function">≲-trans</a> <a id="14457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14437" class="Bound">A≲B</a> <a id="14461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14443" class="Bound">B≲C</a>

  <a id="≲-Reasoning._≲-∎"></a><a id="14468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14468" class="Function Operator">_≲-∎</a> <a id="14473" class="Symbol">:</a> <a id="14475" class="Symbol">∀</a> <a id="14477" class="Symbol">(</a><a id="14478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14478" class="Bound">A</a> <a id="14480" class="Symbol">:</a> <a id="14482" class="PrimitiveType">Set</a><a id="14485" class="Symbol">)</a>
      <a id="14493" class="Comment">-----</a>
    <a id="14503" class="Symbol">→</a> <a id="14505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14478" class="Bound">A</a> <a id="14507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11687" class="Record Operator">≲</a> <a id="14509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14478" class="Bound">A</a>
  <a id="14513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14513" class="Bound">A</a> <a id="14515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14468" class="Function Operator">≲-∎</a> <a id="14519" class="Symbol">=</a> <a id="14521" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12300" class="Function">≲-refl</a>

<a id="14529" class="Keyword">open</a> <a id="14534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14189" class="Module">≲-Reasoning</a>{% endraw %}</pre>

#### 练习 `≃-implies-≲`
{::comment}
#### Exercise `≃-implies-≲`
{:/}

证明每个同构蕴含了一个嵌入。
{::comment}
Show that every isomorphism implies an embedding.
{:/}
<pre class="Agda">{% raw %}<a id="14721" class="Keyword">postulate</a>
  <a id="≃-implies-≲"></a><a id="14733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14733" class="Postulate">≃-implies-≲</a> <a id="14745" class="Symbol">:</a> <a id="14747" class="Symbol">∀</a> <a id="14749" class="Symbol">{</a><a id="14750" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14750" class="Bound">A</a> <a id="14752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14752" class="Bound">B</a> <a id="14754" class="Symbol">:</a> <a id="14756" class="PrimitiveType">Set</a><a id="14759" class="Symbol">}</a>
    <a id="14765" class="Symbol">→</a> <a id="14767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14750" class="Bound">A</a> <a id="14769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5537" class="Record Operator">≃</a> <a id="14771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14752" class="Bound">B</a>
      <a id="14779" class="Comment">-----</a>
    <a id="14789" class="Symbol">→</a> <a id="14791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14750" class="Bound">A</a> <a id="14793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11687" class="Record Operator">≲</a> <a id="14795" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14752" class="Bound">B</a>{% endraw %}</pre>

<pre class="Agda">{% raw %}<a id="14822" class="Comment">-- 在此处书写你的代码</a>{% endraw %}</pre>

#### 练习 `_⇔_` {#iff}
{::comment}
#### Exercise `_⇔_` {#iff}
{:/}

按下列形式定义命题的等价性（又名“当且仅当“）：
{::comment}
Define equivalence of propositions (also known as "if and only if") as follows:
{:/}
<pre class="Agda">{% raw %}<a id="15048" class="Keyword">record</a> <a id="_⇔_"></a><a id="15055" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15055" class="Record Operator">_⇔_</a> <a id="15059" class="Symbol">(</a><a id="15060" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15060" class="Bound">A</a> <a id="15062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15062" class="Bound">B</a> <a id="15064" class="Symbol">:</a> <a id="15066" class="PrimitiveType">Set</a><a id="15069" class="Symbol">)</a> <a id="15071" class="Symbol">:</a> <a id="15073" class="PrimitiveType">Set</a> <a id="15077" class="Keyword">where</a>
  <a id="15085" class="Keyword">field</a>
    <a id="_⇔_.to"></a><a id="15095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15095" class="Field">to</a>   <a id="15100" class="Symbol">:</a> <a id="15102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15060" class="Bound">A</a> <a id="15104" class="Symbol">→</a> <a id="15106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15062" class="Bound">B</a>
    <a id="_⇔_.from"></a><a id="15112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15112" class="Field">from</a> <a id="15117" class="Symbol">:</a> <a id="15119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15062" class="Bound">B</a> <a id="15121" class="Symbol">→</a> <a id="15123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15060" class="Bound">A</a>{% endraw %}</pre>
证明等价性是自反、对称和传递的。
{::comment}
Show that equivalence is reflexive, symmetric, and transitive.
{:/}

<pre class="Agda">{% raw %}<a id="15247" class="Comment">-- 在此处书写你的代码</a>{% endraw %}</pre>

#### 练习 `Bin-embedding` （延伸） {#Bin-embedding}
{::comment}
#### Exercise `Bin-embedding` (stretch) {#Bin-embedding}
{:/}

回忆练习 [Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#Bin) 和
[Bin-laws]({{ site.baseurl }}{% link out/plfa/Induction.md%}#Bin-laws) 中，
我们定义了一个数据类型来表示二进制比特串来表示自然数：
{::comment}
Recall that Exercises
[Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#Bin) and
[Bin-laws]({{ site.baseurl }}{% link out/plfa/Induction.md%}#Bin-laws)
define a datatype of bitstrings representing natural numbers:
{:/}
<pre class="Agda">{% raw %}<a id="15671" class="Keyword">data</a> <a id="Bin"></a><a id="15676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15676" class="Datatype">Bin</a> <a id="15680" class="Symbol">:</a> <a id="15682" class="PrimitiveType">Set</a> <a id="15686" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="15694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15694" class="InductiveConstructor">nil</a> <a id="15698" class="Symbol">:</a> <a id="15700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15676" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="15706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15706" class="InductiveConstructor Operator">x0_</a> <a id="15710" class="Symbol">:</a> <a id="15712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15676" class="Datatype">Bin</a> <a id="15716" class="Symbol">→</a> <a id="15718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15676" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="15724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15724" class="InductiveConstructor Operator">x1_</a> <a id="15728" class="Symbol">:</a> <a id="15730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15676" class="Datatype">Bin</a> <a id="15734" class="Symbol">→</a> <a id="15736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15676" class="Datatype">Bin</a>{% endraw %}</pre>
我们要求你来定义下列函数：
{::comment}
And ask you to define the following functions
{:/}

    to : ℕ → Bin
    from : Bin → ℕ

其满足如下性质：
{::comment}
which satisfy the following property:
{:/}

    from (to n) ≡ n

使用上述条件，证明存在一个从 `ℕ` 到 `Bin` 的嵌入。
{::comment}
Using the above, establish that there is an embedding of `ℕ` into `Bin`.
{:/}
<pre class="Agda">{% raw %}<a id="16087" class="Comment">-- 在此处书写你的代码</a>{% endraw %}</pre>

为什么 `to` 和 `from` 不能构造一个同构？
{::comment}
Why do `to` and `from` not form an isomorphism?
{:/}

## 标准库
{::comment}
## Standard library
{:/}

标准库中可以找到与本章节中相似的定义：
{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}
<pre class="Agda">{% raw %}<a id="16384" class="Keyword">import</a> <a id="16391" href="https://agda.github.io/agda-stdlib/Function.html" class="Module">Function</a> <a id="16400" class="Keyword">using</a> <a id="16406" class="Symbol">(</a><a id="16407" href="https://agda.github.io/agda-stdlib/Function.html#769" class="Function Operator">_∘_</a><a id="16410" class="Symbol">)</a>
<a id="16412" class="Keyword">import</a> <a id="16419" href="https://agda.github.io/agda-stdlib/Function.Inverse.html" class="Module">Function.Inverse</a> <a id="16436" class="Keyword">using</a> <a id="16442" class="Symbol">(</a><a id="16443" href="https://agda.github.io/agda-stdlib/Function.Inverse.html#2193" class="Function Operator">_↔_</a><a id="16446" class="Symbol">)</a>
<a id="16448" class="Keyword">import</a> <a id="16455" href="https://agda.github.io/agda-stdlib/Function.LeftInverse.html" class="Module">Function.LeftInverse</a> <a id="16476" class="Keyword">using</a> <a id="16482" class="Symbol">(</a><a id="16483" href="https://agda.github.io/agda-stdlib/Function.LeftInverse.html#2641" class="Function Operator">_↞_</a><a id="16486" class="Symbol">)</a>{% endraw %}</pre>
标准库中的 `_↔_` 和 `_↞_` 分别对应了我们定义的 `_≃_` 和 `_≲_`，
但是标准库中的定义使用起来不如我们的定义方便，因为标准库中的定义依赖于一个嵌套的记录结构，
并可以由任何相等性的记法来参数化。
{::comment}
The standard library `_↔_` and `_↞_` correspond to our `_≃_` and
`_≲_`, respectively, but those in the standard library are less
convenient, since they depend on a nested record structure and are
parameterised with regard to an arbitrary notion of equivalence.
{:/}

## Unicode

本章节使用了如下 Unicode：
{::comment}
This chapter uses the following unicode:
{:/}

    ∘  U+2218  环运算符 (\o, \circ, \comp)
    λ  U+03BB  小写希腊字母 LAMBDA (\lambda, \Gl)
    ≃  U+2243  渐进相等 (\~-)
    ≲  U+2272  小于或等价于 (\<~)
    ⇔  U+21D4  左右双箭头 (\<=>)
