# Functions

## A first trap

As you have already seen (have you?), functions among types are *primitive notions*, so we do not expect to find a definition for them. But sometimes we want to speak about functions among *sets*, and indeed **functions among sets are different gadgets than functions among types**. This requires a small change of perspective.

Let's inspect the following code:
```lean
example (α β : Type) (S : Set α) (T : Set β) (f g : S → T) :
    f = g ↔ ∀ a : α, a ∈ S → f a = g a :=
```
+++ It *seems* to say that given two functions `f, g` whose domain is a set `S` of elements in `α`, they are equal if and only if they coincide on every element of the domain, yet... `⌘`

The above example shows that what really happens is that functions `f : α → β` can be *upgraded* to functions between sets, by seeing it as a function from the _subtype_ defined by the property that defines the set. This reminds — for instance — the way that in "old-school, pen-and-paper, mathematics" a function $\varphi : X/\mathcal{R} \to Y$ on a quotient can be lifted to a function on $X$ by declaring that $\varphi(x)=\varphi(\overline{x})$: in both cases, we get something "natural" but it is safe to keep in mind that they are not really "the same thing".
+++

## Operations

Given a function `f : α → β` and sets `(S : Set α), (T : Set β)`, there are some constructions and properties that we are going to study:

+++ The image of `S` through `f`, noted `f '' S`.
This is the *set* `f '' S : Set β` whose defining property is
```lean
f'' S := fun b ↦ ∃ x, x ∈ S ∧ f x = b
```
"Unfortunately" it comes with a lot of accents (but we're in France...): and with a space between `f` and `''`: it is not `f'' S`, it is `f '' S`.

`⌘`
+++

+++ The range of `f`, equivalent to `f '' univ`.
I write *equivalent* because the defining property is
```lean
range f := (fun b ↦ ∃ x, f x = b) : β → Prop = (Set β)
```
This is not the verbatim definition of `f '' univ` ...
+++

+++ The preimage of `T` through `f`, noted `f ⁻¹' T`.
This is the set
```lean
f ⁻¹' T : Set α := fun a ↦ f a ∈ T
```
This also comes with one accent and _two_ spaces; the symbol `⁻¹` can be typed as `\^-1`.
+++

+++ The function `f` is **injective on `S`**, denoted by `InjOn f S` if it is injective (a notion defined for functions **between types**) when restricted to `S`: this reads
```lean
def : InjOn f S := ∀ x₁ ∈ S, ∀ x₂ ∈ S, f x₁ = f x₂ → x₁ = x₂
```

In particular, the following equivalence is not a tautology:
```lean
example : Injective f ↔ InjOn f univ
```
it is rather _an exercise for you_...
+++

# Inductive Types and Inductive Predicates