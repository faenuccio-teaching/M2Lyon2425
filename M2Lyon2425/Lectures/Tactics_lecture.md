# An overview of Metaprogramming 

+++ Acknowledgments
<div style="text-align: right">
<font size="4"> 
And down went Mr Pickwick's remark, in Count Smorltork's tablets, with such variations and additions as the Count's exuberant fancy suggested, or his imperfect knowledge of the language, occasioned.

_C. Dickens_
</font>
</div>

Some of the examples below are taken from Rob Lewis' course taught at Brown University in
Winter 2023. Others are taken by [a series of Youtube lectures by Siddhartha Gadgil](https://www.youtube.com/playlist?list=PL_bVGic_CrGtMw1QVFRLRsZjcymm56mRi). I thank them both warmly for letting me use them.

The main reference for these topics is the very beautiful book [Metaprogramming in Lean](https://leanprover-community.github.io/lean4-metaprogramming-book/), together with [Functional Programming in Lean](https://leanprover.github.io/functional_programming_in_lean/) for all aspects (and exercises) concerning monads.

Metaprogramming is a *huge* subject, and we're going to simply give a quick glance. I am **not an expert**.
+++

## Macros

Macros are simply ways of creating a new tactic by packing existing tactics together. The syntax is

```lean
macro "name_of_your_tactic" : tactic =>
  `(tactic | *your sequences of tactics*)
```

+++ Notes
* if you want to insert a variable that you might call later (like in `intro h`) or that is already in scope (like in `cases h`), this is an
 "identifier" and you can insert it as a variable by typing `ids:ident`. To call it later, you use a
 dollar, as in `$ids:ident` (with its type).
* You can also require that square brackets (or parenthesis, or other stuff) are used by doing

```lean
macro "foo" "[" ids:ident "]" : tactic => ...
```

* You need a backtick before the parenthesis in `tactic` otherwise what you are writing gets
compiled, and not stored.
* If you want to add several tactics on several lines, **use parenthesis**.

`⌘`
+++

## Interlude: Monads

Monads are typeclasses for functions `m : Type* → Type*`  with some
extra-property: 

    class Monad (m : Type* → Type*) where
    pure : α → m α                 -- an "embedding" of α` in m α
    bind : m α → (α → m β) → m β   -- lifts f : α → m β to f : m α → m β.

(a compatibility is required between `pure` and `bind`, but we neglect it).

* One example of a monad is `Option α`: it is the type of terms either of the form `some a` for `a : α`, or equal to the extra-term `none : Option α`. Here, 

      pure (a : α) = some a
      bind (some a) = some f a
      bind none f = none

  `Option` is useful to encode errors: `List.get : ℕ → List α → Option (List α)`, so that `L.get n = none` whenever `n > L.length`.


* Another useful example is `State σ α` where `σ : Type` is some "state-carrying" type (typically `σ = ℕ`): it is simply

      def State (σ : Type) (α : Type) : Type := σ → (σ × α)

so a term sends a state to a *pair* of a (possibly updated) state, and an `a : α`. The monad here is `m := State σ` (for fixed `σ`), and its monad instance comes from

    pure (a : α) := fun s ↦ (s, a) (: σ ↦ σ × α)
    bind n f :=               -- here n : State σ a; and f : α → State σ β
      fun s ↦
        let (s', a) := n s            -- recall that n s : σ × α
        (f a) s'
        
  since `f a : State σ β = σ → σ × β`, the final `f a s'` has type `σ × β`, and therefore `bind n f : σ → σ × β`

This monad is useful to store values with a "state".

`⌘`

+++ `do` and `←`
When working with monads, two crucial syntax are at our disposal: `do` simply allows you to do imperative programming inside a `def`.

The syntax `let ←` is an improvement of `bind`:
+++

## Going Meta
+++ Expressions and variables
Expressions are the most basic objects Lean deals with, and they can virtually be anything. They are defined as the following inductive type:

```lean
inductive Expr where
  | bvar    : Nat → Expr                              -- bound variables
  | fvar    : FVarId → Expr                           -- free variables
  | mvar    : MVarId → Expr                           -- meta variables
  | sort    : Level → Expr                            -- Sort
  | const   : Name → List Level → Expr                -- constants
  | app     : Expr → Expr → Expr                      -- application
  | lam     : Name → Expr → Expr → BinderInfo → Expr  -- lambda
  | forallE : Name → Expr → Expr → BinderInfo → Expr  -- depnd't arrows
  | letE    : Name → Expr → Expr → Expr → Bool → Expr -- let expressions
  -- less essential constructors:
  | lit     : Literal → Expr                          -- literals
  | mdata   : MData → Expr → Expr                     -- metadata
  | proj    : Name → Nat → Expr → Expr                -- projection
```
All constructors above construct things whose meaning should be pretty clear, except potentially for free and meta variables (`lit`, `mdata` and `proj` can be forgotten for now): we'll inspect those later.

`⌘`

+++ Variables


Free- and Metavariables play a special role. 

### Free variables 
Free variables are the "usual ones", like the variable `x` in `x + 2`. They do not even to actually be typed, they've simply got an identifier `FVarId`.


`⌘`


### Metavariables 


To quote Lean's documentation,
```
Metavariables are used to represent "holes" in expressions, and goals in the tactic framework. Metavariable declarations are stored in the MetavarContext. Metavariables are used during elaboration, and are not allowed in the kernel, or in the code generator.
```
Each metavariable has a unique name, usually rendered as `?m` or `?m_197`, and a target type `T` which is *explicit*. It comes with a local context containing hypotheses (the `Γ` such that `Γ ⊢ ?m : T` is well-typed).

Both "holes" to be filled by type-inference and, most importantly, **goals** are represented by metavariables. To close a goal, we must provide an expression `e` of the target type `T`: internally, closing a goal corresponds to assigning the value `e` to the metavariable; we write `?m := e` for this assignment.

To "play" with metavariables we need our code to be *elaborated* somewhere, so what typically happens is that we `def`ine some code (possibly acting on metavariables, that do not exist at the moment of our writing) and then we declare some `elab`oration procedure where we see this code in action.

`⌘`


+++

+++ Creating new tactics
This all relies on a monad `TacticM`: as it turns out, there are *zillions* of monads all over `Lean` and `Mathlib`, and *thousands* of "moral
interpretations" thereof. Concerning `TacticM  α`, you might think of its terms as actions that
1. perform some tactic; and then
1. return a term in `α`.


#### Warm-up
Let's begin by implementing two tactics, one (`Count`) that simply counts the number of variables in the
context and one (`ExtrFn`) that extract all variables that are functions.

```lean
partial def Count : TacticM Unit :=
  (do
    let lctx ← getLCtx
    let n := lctx.decls.toList.length
    do logInfo m!"{n - 1}")
```

Terms in `TacticM Unit` simply perform the tactic, since `Unit` only contains `_`.
```lean
partial def ExtrFn : TacticM Unit :=
  (do
    let mut xs := #[]
    let lctx ← getLCtx
    for lh in lctx do
      if !lh.index == 0 && lh.type.isForall 
        then xs := xs.push lh.userName
    do logInfo m!"{xs}"
    return)
```
* `let mut` introduces a _mutable_ variable (Lean is a functional programming language!) so that 
the final `let xs :=...` works.

* `getLCtx` returns the local context, and `lctx` is the array containing it; for each `lh` in `lctx`,
we can get its type through `lh.type`. Then we check if `lh` is a function: this is precisely when its type
`lh.type` is a `∀` (a "forall", also called a Π-type).

`logInfo` is the tactic writing some message in the info-views: in VSCode
this also shows up in the main window (in another colour).

```lean
elab "count_variables" : tactic => Count
elab "show_fn_var" : tactic => ExtrFn
```

` elab` is the command enforcing some definition as a tactic
-/
+++