# Sets

## Introduction
Sets are **primitive** objects when doing classical, old-school, pen-and-paper mathematics: there is no *definition* of what a set is, there are only *rules* about how these objects work, governing their behaviour under unions, intersections, etc. 

Concretely, that's all you need: one rarely (never?) uses that in set-theoretic language a function between $S$ and $T$ is really a subset of $S\times T$ satisfying some property.

Mathematical objects that are normally represented by a set (like a group, a ring, a differentiable manifold, the set of prime numbers, a Riemann surface, the positive reals, etc...) are formalised in Lean as *types* endowed with some extra-structure.

So, for Lean, sets are **no longer primitive objects**; yet sometimes we really want to speak about *sets* as collections of elements and to play the usual games. This is possible, and the same ``working'' rules hold.


## Definitions

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

You can think of this function as being the characteristic function of `S`; indeed, the `∈` symbol means that the value of `S` is `True`. So `x ∈ S` is the proposition that is true when `x` belongs to `S` and is false otherwise. So, the positive integers are a *function*!

### Some examples: 
1. How to prove that something belongs to a set?
1. Positive integers;
1. Even numbers'
1. An abstract set of `α` given by some `P`.
+++

+++ Sub(sub-sub-sub)sets are not treated as sets-inside-sets.

Let's think old-stylish for a moment:

Given a set $S$, what is a subset $T$ of $S$ *for you*?
1. Another set such that $x\in T\Rightarrow x \in S$.
1. A collection of elements of $S$.
1. ... is there **any difference** whatsoever?!

*Yes and No*: you can either stress the fact that $T$ is a honest set satisfying some property; or the fact that it is a set whose elements "come from" $S$. We take the **first approach**.


So, given two sets  `S T : Set α`, the property that `T` is a subset of `S` is *an implication*
```lean
def (T ⊆ S : Prop) := ∀ a, a ∈ T → a ∈ S
```

Yet, we can _upgrade_ sets to types and we can speak of a `T : Set S` for some `S : Set α`, where we 
really mean `T : Set ↑S = Set (S : Type*)`.

+++

## Operations on Sets
+++ Intersection
Given sets `S T : Set α` we have the
```lean
def (S ∩ T : Set α) := fun a => a ∈ S ∧ a ∈ T
```
On the way of proving a simple statement about self-intersection, we encounter **extensionality**: this is the principle saying that equality of sets (or set-like objects...) can be checked on elements. It is really based on _Propositional extensionality_ saying that two propotions are equal if and only if they have the same truth values.

+++

+++ Union
Given sets `S T : Set α` we have the
```lean
def (S ∪ T : Set α) := fun a => a ∈ S ∨ a ∈ T
```

And if `S : Set α` but `T : Set β`? **ERROR!**
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



+++ Set complement and difference
Given a set `S : Set α`, its complement is defined by the negation of the membership property, and it is denoted `Sᶜ`.
```lean
Sᶜ = {a : α | ¬a ∈ S}
```

Similarly, given sets `S T : Set α`, we can define their difference `S \ T : Set α`, that corresponds to the property (where `a ∉ T` means of course `¬ a ∈ T`)
```lean
def (S \ T : Set α) = fun a => a ∈ S ∧ ¬ a ∈ T
def (S \ T : Set α) = fun a => a ∈ S ∧ a ∉ T
```

Let's see now some examples about all this.
+++

+++ Indexed intersection and union
Instead of intersecting and taking unions of *two* sets, we can allow fancier indexing sets (that will actually be *types*, *ça va sans dire*): more on this in the exercise sheets.
+++

