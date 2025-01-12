# Forgetful inheritance

As discussed in the last lecture, forgetful inheritance is the right way to ensure that extending
structures does not lead to problematic diamonds: remember that diamonds are not a problem *per se*,
they are perfectly fine so long they lead to **definitionally equal** terms.

The term *forgetful inheritance*, and its slogan, are due to Affeldt, Cohen, Kerjean, Mahboubi,
Rouhling and Sakaguchi in their work https://inria.hal.science/hal-02463336v2 :
```quote
The solution to the problems [explained in this section] is to ensure definitional equality by including poorer structures into richer ones; this way, "deducing" one structure from  the other always amounts to erasure of data, and this guarantees there is a unique and canonical way of getting it. We call this technique forgetful inheritance, as it is reminiscent of forgetful functors in category theory.
```

*Slogan:* **include poorer structures in richer ones.**

## An example

The following example is extracted from Affeldt *et al.*'s work quoted above.

Idea: 
1. Normed modules `M`, (additive) abelian groups with a `ℝ`-valued norm `‖ ⬝ ‖ : M → ℝ`.
1. Modules with a `Prop`-valued relation `rel : M → M → Prop`.
1. Every normed module gives rise to the relation "being in the same ball of radius `1`: in this sense, *normed modules are a richer structure than modules with a relation*.
`⌘`

Both structures can be extended to (binary) products: 

4. Given a pair of normed modules `M, N`, we can put the `sup` norm on `M × N`.
5. Given a pair of modules `M, N` with relations `rel_M` and `rel_N` we can put the `∧`-relation `rel_M ∧ rel_N` on `M × N`.
6. Obtain the diagram
$$
 \begin{CD}
 M_{\mathrm{Normed}} × N_{\mathrm{Normed}} @>4.>> (M × N)_{\mathrm{Normed}}\\
 @VV3.V @VV3.V\\
 M_{\mathrm{WithRel}} × N_{\mathrm{WithRel}} @>5.>> (M × N)_{\mathrm{WithRel}}\\
 \end{CD}
$$

+++ It does not commute.

To see this, let's suppose that, for every type `T`, we have a `Prop`-valued function `p` leaving
from the type `T → Prop`, so

    p : ∀ {T : Type}, (T → Prop) → Prop

In particular, given a
`ModuleWithRel` `M` and a term `m : M`, we have `rel m : M → Prop`, so `p (rel m) : Prop`
(*i. e.* `p (rel m) = True` or `p (rel m) = False`).

Let's suppose that whenever the `ModuleWithRel` structure on `M` comes from a
`NormedModule` instance on `M`, `p (rel m) = True` for all `m : M`: we might expect then that if `M`
is a `NormedModule` and `⟨m₁, m₂⟩ : M × M`, then

    p (rel ⟨m₁, m₂⟩) : True

Yet... `⌘`
+++

+++ Why?

This is not working because the `rel` in the goal comes from the `ModuleWithRel` instance on a
product, whereas the `rel` in `hp` comes from the `Rel` instance *deduced* from the
`NormedModule_bad` instance on the product (it suffices to hover on the terms to see this).
+++

+++ A way out?
One (wrong, but instructive) solution would be to avoid declaraing a
`ModuleWithRel` instance on `M × N` 

Try it... `⌘`

Indeed, in this case, the only instance of `ModuleWithRel` that
would be found on `M × M` would be through the path

    ?m₀ : ModuleWithRel M × M ← ?m₁ : NormedModule_bad (M × M)

and therefore the above proof would work.

But if the weaker structure `ModuleWithRel` is (mathematically) reasonable, we  might want to endow
a product of `ModuleWithRel`'s with such a structure *even if they are not normed*`. So, the above
solution does not work, but it might suggest the following trick.

The problem is that passing from `NormedModule_bad` to `ModuleWithRel`
(*i. e*. declaring a `ModuleWithRel` instance on every `NormedModule_bad`)
is not a pure "erasure", because we are not simply throwing away a field, but using some
field in the first (namely `‖ ⬝ ‖`) to construct the term `rel` of the second: this yields to the
problem we have just witnessed.
+++

### The correct way (using forgetful inheritance)
Instead of *deducing* the `ModuleWithRel` instance on any `NormedModule`, we *include* the poorer
structure in the richer one (the slogan...).

    class NormedModule (M : Type*) [AddCommGroup M] where
    norm : M → ℝ
    rel : M → M → Prop := fun m n ↦ norm (m - n) ≤ 1

    instance (M : Type*) [AddCommGroup M] [NormedModule M] : ModuleWithRel M := ⟨NormedModule.rel⟩

The huge difference with what happened for `NormedModule_bad` is that *there* the instance `NormedModule_bad → ModuleWithRel`
contained some **new** data (the definition of `rel`), whereas *here* it is simply a projection, forgetting `norm`.

And then we can define a `NormedModule` instance on the product `M × N` of two `NormedModule`s `M`
and `N` by **using** the `ModuleWithRel` structure on `M × N`, so that `(M × N).rel` will be `defeq`
to `M.rel ∧ N.rel`.

`⌘`

* **Remark:** The `rel v` in the goal is still the `rel` coming from the `ModuleWithRel` instance on a
product, and the `rel` in `hp` still comes from the `ModuleWithRel` instance deduced from the
`NormedModule` structure on `M × M`, as in the first example. But now this second instance is simply
obtained from the first by forgetting a field, so in particular it *coincides definitionally* with
the previous one. This is another way of looking at why the seemingly odd declaration `rel := rel`
in the `NormedModule` instance on `M × N` makes sense.

+++ A drawback

From the point of view of constructing a library, the above solution can be painful.

What can we do if we already have a class and we want to later insert something "below" it (*i. e.* to create
a class that is more general than the first we had, so that every element of the first will have an
instance of the second)? We will need to modify the first one, adding to all fields of the second
**although they can be deduced rather than be imposed**; and let the instance "from the first to the
second" be simply a projection.

* For an example of this, together with the description of the pain it caused, see
https://github.com/leanprover-community/mathlib3/pull/7084 (it's Lean3, but you can see the point): 117 files were changed.


