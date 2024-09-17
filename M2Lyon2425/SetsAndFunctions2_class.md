# Sets and Functions

## Introduction
Sets are **primitive** objects when doing classical, old-school, pen-and-paper mathematics: there is no *definition* of what a set is, there are only *rules* about how these objects work, governing their behaviour under unions, intersections, etc. For Lean, sets are **no longer primitive objects**, but the same rules hold.


In the same vein, for Lean functions are **primitive** objects: there is no *definition* of what a function (between two "types") is, there are only **rules** about how these fundamental objects behave.

Concretely, that's all you need: one rarely (never?) uses that in set-theoretic language a function between $S$ and $T$ is really a subset of $S\times T$ satisfying some property.

## Sets

Mathematical objects that are normally represented by a set (like a group, a ring, a differentiable manifold, the set of prime numbers, a Riemann surface, the positive reals, etc...) are formalised in Lean as *types* endowed with some extra-structure.

Yet sometimes we really want to speak about *sets* as collections of elements and to play the usual games.

### Basic features

+++ Every set lives in a given type: it is a set of elements (*terms*) of a type:
```lean
variable (α : Type) (S : Set α)
```
expresses that `α` is a type and `S` is a set of elements/terms of the type `α`. On the other hand,
```lean
variable (S : Set)
```
does not mean "let `S` be a set": it means nothing and it is an error.
+++

+++ A set **coincides** with the test-function defining it.

 Given a type `α`, a set `S` (of elements/terms of `α`) is a *function*
```lean
S : α → Prop
```
so `(Set α) = (α → Prop)`.

You can think of this function as being the characteristic function of `S`; indeed, the `∈` symbol means that the value of `S` is `True`:
```lean
example (α : Type) (x : α) (S : Set α) : x ∈ S ↔ S x := rfl
```
You might think that `x ∈ S` is the proposition that is true when `x` belongs to `S` and is false otherwise. So, the positive reals are a *function*!

Nevertheless, a general principle of formalized mathematics is that you shuold rely on an API (_Application Programming Interface_) rather than definitional equality.
+++

+++ Sub(sub-sub-sub)sets are not treated as sets-inside-sets.

Let's think old-stylish for a moment:
+++ Given a set $S$, what is a subset $T$ of $S$ *for you*?
1. Another set such that $x\in T\Rightarrow x \in S$.
1. A collection of elements of $S$.
1. ... is there **any difference** whatsoever?!

*Yes and No*: you can either stress the fact that $T$ is a honest set satisfying some property; or the fact that it is a set whose elements "come from" $S$. We take the **first approach**.

<!-- <br>
 -->
So, given two sets  `S T : Set α`, the property that `T` is a subset of `S` is an *implication*
```lean
def (T ⊆ S : Prop) := ∀ a, a ∈ T → a ∈ S
```
Let's see some examples: 
1. Positive integers
1. Even numbers
1. An abstract set of `α` given by some `P`
+++

### Main constructions
+++ Intersection
Given sets `S T : Set α` we have the
```lean
def (S ∩ T : Set α) := fun a => a ∈ S ∧ a ∈ T
```
On the way of proving a simple statement about self-intersection, we encounter **extensionality**: this is the principle saying equality of sets (or set-like objects...) can be checked on elements.

+++

+++ Union
Given sets `S T : Set α` we have the
```lean
def (S ∪ T : Set α) := fun a => a ∈ S ∨ a ∈ T
```

And if `S : Set α` but `T : Set β`?
+++

+++ The empty set and the universal set
The first is the constant function `False : Prop` (and not `false : Bool`!)
```lean
def (∅ : Set α) := fun a => False
```
While the second (containing all terms of `α`) is the constant function `True`
```lean
def (univ : Set α) := fun a => True
```
**Bonus**: There are infinitely many empty sets!

+++

+++ Set difference
Given sets `S T : Set α`, we can define their difference `S \ T : Set α`, that corresponds to the property (where `a ∉ T` means of course `¬ a ∈ T`)
```lean
def (S \ T : Set α) = fun a => a ∈ S ∧ ¬ a ∈ T
def (S \ T : Set α) = fun a => a ∈ S ∧ a ∉ T
```

Let's see now an example combining subtraction and the empty set.
+++

+++ Indexed intersection and union
Instead of intersecting and taking unions of *two* sets, we can allow fancier indexing sets (that will actually be *types*, *ça va sans dire*): more on this in the exercise sheets.
+++


## Functions

As said, *functions among types are primitive notions*, so we do not expect to find a definition for them. But we want to speak about functions among *sets*, and indeed **functions among sets are different gadgets than functions among types**. This requires a small change of perspective.

Let's inspect the following code:
```lean
example (α β : Type) (S : Set α) (T : Set β) (f g : S → T) :
    f = g ↔ ∀ a : α, a ∈ S → f a = g a :=
```
+++ It *seems* to say that given two functions `f, g` whose domain is a set `S` of elements in `α`, they are equal if and only if they coincide on every element of the domain, yet...

```
application type mismatch
  f a
argument
  a
has type
  α : Type
but is expected to have type
  ↑S : Type
```

The above example shows that what really happens is that functions `f : α → β` can be *upgraded* to functions between sets. This reminds — for instance — the way that in "old-school, pen-and-paper, mathematics" a function $\varphi : X/\mathcal{R} \to Y$ on a quotient can be lifted to a function on $X$ by declaring that $\varphi(x)=\varphi(\overline{x})$: in both cases, we get something "natural" but it is safe to keep in mind that they are not really "the same thing".
+++

### Main constructions

Given a function `f : α → β` and sets `(S : Set α), (T : Set β)`, there are some constructions or properties we can analyze:

+++ The image of `S` through `f`, noted `f '' S`.
This is the *set* `f '' S : Set β` whose defining property is
```lean
f'' S := fun b => ∃ x, x ∈ S ∧ f x = b
```
So, you can upgrade a function `f` to a function between the types of sets.
+++

+++ The range of `f`, equivalent to `f '' univ`.
I write *equivalent* because the defining property is
```lean
range f := (fun b => ∃ x, f x = b) : β → Prop = (Set β)
```
This is not the verbatim definition of `f '' univ` ...
+++

+++ The preimage of `T` through `f`, noted `f ⁻¹' T`.
This is the set
```lean
f ⁻¹' T : Set α := fun a => f a ∈ T
```

+++

+++ The function `f` is **injective on `S`**, denoted by `InjOn f S` if it is injective (a notion defined for functions **between types**) when restricted to `S`: this reads
```lean
def : InjOn f S := ∀ x₁ ∈ S, ∀ x₂ ∈ S, f x₁ = f x₂ → x₁ = x₂
```

In particular, the following equivalence is not a tautology:
```lean
example : Injective f ↔ InjOn f univ
```

Let's finish proving it, then!
+++