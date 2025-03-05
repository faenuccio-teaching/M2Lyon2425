import Lean.Elab
import Mathlib.Tactic
import Mathlib.Topology.Basic

set_option linter.unusedTactic false
set_option linter.unusedVariables false

open scoped PiNotation

open Lean Meta Elab Tactic

-- #1 Macros
section macros

example (α β : Type) (a b : α) (f : α → β) : a = b → f a = f b := by
  intro h
  cases h
  rfl

example : ∀ n : ℕ, 0 ≤ n := by
  intro n
  cases n
  rfl   -- BTW: can you see why it works? Because `le_refl` is tagged `@refl`
        -- and `rfl` as tactic is actually `apply_refl`.
  sorry


example (α : Type) (a : α) :
  ∀ (L : List α), a :: L = (a :: L.drop L.length) ++ (L.take L.length) := by
  intro L
  cases L
  rfl
  sorry

-- Let's try to make this into a `macro`:

macro "cases_rfl" : tactic =>
  `(tactic | (intro h -- this h will *NOT* overwrite existing variables
              cases h
              rfl)) -- try also withouth `)`

example (α β : Type) (a b : α) (f : α → β) : a = b → f a = f b := by
  cases_rfl

example : ∀ n : ℕ, 0 ≤ n := by
  cases_rfl
  sorry

example (α : Type) (a : α) : ∀ (L : List α), a :: L = (a :: L.drop L.length) ++ (L.take L.length) := by
  cases_rfl
  sorry

-- # Another example

lemma abcd_bdc (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) : b ∧ d ∧ c := by
  apply And.intro
  · rcases h with ⟨ha, hbcd⟩
    rcases hbcd with ⟨hbc, hd⟩
    rcases hbc with ⟨hb, hc⟩
    assumption
  apply And.intro
  · sorry
  · sorry

lemma abcd_bacb (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) : b ∧ (a ∧ (c ∧ b)) := by
  apply And.intro
  · rcases h with ⟨ha, hbcd⟩
    rcases hbcd with ⟨hbc, hd⟩
    rcases hbc with ⟨hb, hc⟩
    assumption
  · apply And.intro
    · sorry
    · apply And.intro
      · sorry
      · sorry

-- Can this be improved? Perhaps the following works...
macro "split_and" "[" ids:ident "]": tactic =>
  `(tactic| repeat' ( apply And.intro
                      rcases $ids:ident))

lemma abcd_bdc₁ (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) : b ∧ d ∧ c:= by
  split_and [h]
  repeat' sorry

lemma abcd_bacb₁ (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) : b ∧ (a ∧ (c ∧ b)) := by
  split_and [h]
  repeat' sorry

-- *Somewhat good* but **not really good**... → `⌘`


end macros

section Expressions
-- # Expressions

-- Create expression 1 + 2 with Expr.app
-- Create expression fun x y => x + y
-- Create expression fun (p : Prop) => (λ hP : p => hP).
-- [Universe levels] Create expression Type 6

-- `⌘`

/-Ex1
[Metavariables] Create a metavariable with type Nat, and assign to it value 3.
Notice that changing the type of the metavariable from Nat to, for example, String, doesn't raise
any errors - that's why, as was mentioned, we must make sure "(a) that val must have the target type
 of mvarId and (b) that val must only contain fvars from the local context of mvarId".
-/

-- # Metavariables

def one : MetaM Unit := do
  let mv ← mkFreshExprMVar (Expr.const `Nat []) (userName := `hy)
  -- mv.mvarId!.assign (mkNatLit 3) -- try before and after commenting
  IO.println s!"The value of the new metavariable is {← instantiateMVars mv}"

#eval show MetaM _ from do
  one


  /-Ex3
  [Metavariables] Consider the theorem red, and tactic explore below. a) What would be the type
  and userName of metavariable mvarId? b) What would be the types and userNames of all local
  declarations in this metavariable's local context? Print them all out.-/

  -- set_option pp.natLit false

  elab "explore" : tactic => do
    let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
    let metavarDecl : MetavarDecl ← mvarId.getDecl

    logInfo "Our metavariable"
    logInfo mvarId
    -- [anonymous] : 2 = 2
    -- logInfo s!"\n{metavarDecl.userName} : {metavarDecl.type}"

    logInfo "\n All of its local declarations"
    let localContext : LocalContext := metavarDecl.lctx
    for (localDecl : LocalDecl) in localContext do
      if localDecl.isImplementationDetail then
        -- (implementation detail) red : 1 = 1 → 2 = 2 → 2 = 2
        logInfo m!"\n(implementation detail) {localDecl.userName} : {localDecl.type}"
      else
        -- hA : 1 = 1
        -- hB : 2 = 2
        logInfo m!"\n{localDecl.userName} : {localDecl.type}"


  theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
  explore
  sorry


end Expressions

section Monads
-- ## Monads

/- ### An example: f/Fibonacci numbers
The following definition is infamously slow as values are repeatedly computed -/

def fib : Nat → Nat
| 0 => 1
| 1 => 1
| k + 2 => fib k + fib (k + 1)

set_option trace.profiler true in
#eval fib 32

/- #### The `FibM` State Monad -/
structure myState (σ α : Type*) where
  run : σ → α × σ

variable {σ : Type*}

def halt : myState σ σ := ⟨fun s => (s, s)⟩
def update (f: σ → σ) : myState σ Unit := ⟨fun s => ((), f s)⟩

def run' [Inhabited σ] (α : Type*) (x: myState σ α) (s: σ := default) : α
  := (x.run s).1

instance : Monad (myState σ) where
  pure x := ⟨fun s => (x, s)⟩
  bind x f := ⟨fun s =>
    let (a, s') := x.run s
    (f a).run s'⟩

/-!
* We have a background state that is a `HashMap Nat Nat`, to store values already computed.
* When computing a term of type `FibM α` we can `get` and use the state and also `set` or `update` it.
* Future computations automatically use the updated state.
* Using this we can efficiently compose.
-/
-- abbrev FibM := myState (Std.HashMap Nat Nat)
abbrev faeFib := myState (List ℕ)


-- def fibM (n: Nat) : FibM Nat := do
--   let s ← halt
--   match s.get? n with
--   | some y => return y
--   | none =>
--     match n with
--     | 0 => return 1
--     | 1 =>  return 1
--     | k + 2 => do
--       let f₁ ← fibM k
--       let f₂ ← fibM (k + 1)
--       let sum := f₁ + f₂
--       update fun m => Std.HashMap.insert m n sum
--       return sum

-- #check (31 : (faeFib ℕ))

#eval [1,2,3,4].length
#eval [1].get? 1

def pyth (n : ℕ) : faeFib ℕ := do
  ⟨fun (L : List ℕ) ↦ match L.get? n with
    | some y => ⟨y, L⟩ -- il caso in cui `n < L.length`
    | none => match n with -- il caso in cui `L.length ≤ n`
      | 0 => ⟨1, [1]⟩ -- il caso in cui `L` era vuota
      | 1 => ⟨1, [1, 1]⟩ -- il caso in cui `L` aveva un solo elemento
      | k + 2 =>
        let sum : ℕ := ((pyth k).1 L).1 + ((pyth (k+1)).1 L).1
        ⟨sum, L ++ [sum]⟩ -- il caso in cui `L` ha almeno due elementi
    ⟩

def faefibb (n : ℕ) : ℕ := ((pyth n).1 []).1

#synth Repr ℕ

instance : Repr (faeFib ℕ) := by
  constructor
  intro L n
  exact instReprNat.reprPrec (L.1 []).1 n

set_option trace.profiler true in
#eval pyth 32

set_option trace.profiler true in
#eval fib 32
  -- exact (instReprNat.reprPrec (L.1 []).1)
  -- ⟨fun mx n => rep.reprPrec (run' α mx) n⟩

-- #eval faefibb 35

-- set_option trace.profiler true in
-- #eval fib 35

def faefibM (n : ℕ) : faeFib ℕ := do
  let s ← halt
  match s.get? n with
  | some y => return y
  | none =>
    match n with
    | 0 => return 1
    | 1 =>  return 1
    | k + 2 => do
      let f₁ ← faefibM (k)
      let f₂ ← faefibM (k+1)
      let add := f₁ + f₂
      update fun m ↦ m ++ [add]
      return add

#check (faefibM 0)


instance {α : Type*} [rep : Repr α] [Inhabited σ] : Repr (myState σ α) :=
  ⟨fun mx n => rep.reprPrec (run' α mx) n⟩

#eval faefibM 7


end Monads
section elabs
-- # Elaborated tactics


elab "solve" : tactic => do
    let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
    let metavarDecl : MetavarDecl ← mvarId.getDecl
    let locCtx : LocalContext := metavarDecl.lctx
    for ld in locCtx do
      if ← isDefEq ld.type metavarDecl.type then
        mvarId.assign ld.toExpr

theorem red' (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
    solve

partial def Count : TacticM Unit :=
  (do
    let lctx ← getLCtx
    let n := lctx.decls.toList.length
    do logInfo m!"There are {n - 1} variables") -- this `-1`subtracts the goal, which is a Meta-Variable

partial def ExtrFn : TacticM Unit :=
  (do
    let mut xs := #[]
    let lctx ← getLCtx
    for lh in lctx do
      if (LocalDecl.index lh) != 0 && lh.type.isForall
        then xs := xs.push lh.userName
    do logInfo m!"The list of functions in the context is {xs}"
    return)

elab "count_variables" : tactic => Count
elab "show_fun" : tactic => ExtrFn

example (α β : Type) (f g : α → β) (a : α) (h : f a = g a) : True := by
  count_variables
  show_fun
  sorry

example (α : Type) (f g h : α → ℕ) (h : f = g ∨ g = h) : True := by
  show_fun
  cases h
  · show_fun
    sorry
  · show_fun
    sorry

example (α : Type) (h : ∀ f : ℕ → ℕ, f 0 = f 1) : False := by
  show_fun
  sorry

example (α : Type) (I : ℕ → Type) (x : Π (n : ℕ), I n) : False := by
  show_fun
  sorry

-- ## An informative one:

/- While solving the IMO 2024, Google DeepMind came up with a proof, based on [induction on `12]
(https://storage.googleapis.com/deepmind-media/DeepMind.com/Blog/imo-2024-solutions/P2/index.html)
after which, of course, the state was exactly the same. We want to detect this behaviour.

Let's inspect the following proof -/


example (n : ℕ) : n + 1 = 1 + n := by
  induction 12
  repeat' sorry


elab "WhatsThis " n:term : tactic =>
  do
    -- let mvarId ← getMainGoal --the Main Goal as a Metavariable
    -- let metavarDecl : MetavarDecl  ← mvarId.getDecl -- the Main Goal as a Declaration
    let metavarVars ← getLCtx -- the list of free variables in the Main Goal
    for lh in metavarVars do
      if /- n.raw.getId -/ `n == lh.userName then --check whether our term appears in the Goal
        return
      else
         do logInfo m!"Do you really mean {n}?"
    return

macro "DeepMind_induction " ids:term : tactic =>
  `(tactic | (WhatsThis $ids
              induction $ids))

example (n : ℕ) : n + 1 = 1 + n := by
  DeepMind_induction 12
  repeat' sorry



/- ## Back to `∧`
The following tactic destructs *completely* all `p ∧ q` *hypotheses* found in the local context:
more complicated than the macro-defined `split_and` because that one *only acted on the goal*,
here we navigate all assumptions.
-/

partial def DestrAnd : TacticM Unit :=
  withMainContext
    do
      for lh in ← getLCtx do -- get the context
      let eq := Expr.isAppOf lh.type ``And --checks whether `lh` coincides with `?m_1 ∧ ?m_2`
      -- let eq := Expr.isAppOfArity lh.type ``And 2 --checks whether `lh` coincides with `?m_1 ∧ ?m_2`
      if eq then  -- if yes, the code below applies `cases` on `lh`
        liftMetaTactic -- Get goal, run a tactic, add the new goals to the new the goal list
          fun goal ↦ do
            let subgoals ← MVarId.cases goal lh.fvarId --insert new subgoals in the list of goals
            let subgoalsList := subgoals.toList
            pure (List.map (fun subgoal ↦
                InductionSubgoal.mvarId (CasesSubgoal.toInductionSubgoal subgoal))
              subgoalsList)
        DestrAnd -- finally, a recursive call
        return

elab "destruct_and" : tactic => DestrAnd

-- let's see if the family of `abcd_???'s` lemmas improve

lemma abcd_bdc₂ (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) : b ∧ d ∧ c := by
  repeat' apply And.intro
  · destruct_and
    assumption
  · destruct_and
    assumption
  · destruct_and
    assumption

lemma abcd_bacb₂ (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) : b ∧ (a ∧ (c ∧ b)) := by
  repeat' apply And.intro
  · destruct_and
    assumption
  · destruct_and
    assumption
  · destruct_and
    assumption
  · destruct_and
    assumption

lemma abcd_ac (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) : (a ∧ c) := by
  repeat' apply And.intro
  · destruct_and
    assumption
  · destruct_and
    assumption

/- All this calls for a **macro!** -/

macro "close_and" : tactic =>
  `(tactic | (repeat' (repeat' apply And.intro)
                      destruct_and
                      assumption ))

lemma abcd_bdc₃ (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) : b ∧ d ∧ c := by
  close_and

lemma abcd_bacb₃ (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) : b ∧ (a ∧ (c ∧ b)) := by
  close_and

lemma abcd_ac₃ (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) : (a ∧ c) := by
  close_and

-- More modifications of the goal

def findNat' : TacticM (List Expr) :=
  withMainContext
    do
    -- let lctx ← getLocalHyps
    let lctx ← getLCtx -- The local context is basically the list of all metavariables
    let mut nats := #[] -- the `mut` ensure that we're defining a **mutable** variable
    for h in lctx do
      if h.type == .const ``Nat []
        then nats := nats.push h.userName
    do logInfo m!"The list of naturals found in the context is {nats}"
    return List.map (.const · []) nats.toList

def findNat : TacticM Unit :=
  withMainContext
    do
    let lcnats ← findNat'

def findNat'' : TacticM Unit :=
  withMainContext
    do
    let lcnats ← findNat'

elab "findNat" : tactic => findNat

example (n m k : ℕ) (H : n = 3 + 1) : True := by
  let e : ℕ := 3 --removing the `: ℕ` creates problems, actually a stronger monad is needed.
  findNat
  sorry

def SuccNat' : TacticM Unit :=
  withMainContext do
  let lcnats ← findNat'
  for a in lcnats do
  /- `liftMetaTactic` gets the `mvarid` of the main goal, run the given `tactic`,
  then set the new goals to be the resulting goal list.-/
  liftMetaTactic fun mv => do
  /- `mv.assertHypotheses` Convert the given goal `Ctx |- target` into `Ctx, (hs[0].userName : hs[0].type) ... |-target`.
    It assumes `hs[i].val` has type `hs[i].type`. -/
      let mv ← mv.define "`a".toName (.const ``Nat []) (mkNatLit 37)--(Lean.mkAppN (.const ``Nat.mul []) #[mkNatLit 2, a])
  /-Introduce one object from the goal `mvarid`, preserving the name used in the binder.
    Returns a pair made of the newly introduced variable and the new goal.
    This will fail if there is nothing to introduce, *ie* when the goal
    does not start with a `∀`, `λ` or `let`.-/
      let (_, mv) ← mv.intro1P
      return [mv]

def SuccNat : TacticM Unit :=
  withMainContext do
  let lcnats ← getLCtx
  for h in lcnats do
  /- `liftMetaTactic` gets the `mvarid` of the main goal, run the given `tactic`,
  then set the new goals to be the resulting goal list.-/
  if h.type == .const ``Nat [] then
    liftMetaTactic fun mv => do
  /- `mv.assertHypotheses` Convert the given goal `Ctx |- target` into `Ctx, (hs[0].userName : hs[0].type) ... |-target`.
    It assumes `hs[i].val` has type `hs[i].type`. -/
      let mv ← mv.define s!"double_{h.userName.toString}".toName (.const ``Nat [])
          (Lean.mkAppN (.const ``Nat.mul []) #[mkNatLit 2, h.toExpr])
  /-Introduce one object from the goal `mvarid`, preserving the name used in the binder.
    Returns a pair made of the newly introduced variable and the new goal.
    This will fail if there is nothing to introduce, *ie* when the goal
    does not start with a `∀`, `λ` or `let`.-/
      let (_, mv) ← mv.intro1P
      return [mv]

elab "succNat" : tactic => SuccNat

example (n m k : ℕ) (H : n = 3 + 1) : True := by
  succNat
  sorry

-- The `Nat.mul 2 n` is still somewhat annoying, and this comes from our usage of expressions
-- rather than more direct syntax.

def SuccNatStx : TacticM Unit := withMainContext do
  let lctx ← getLCtx
  for h in lctx do
    if h.type == .const ``Nat [] then
      let th ← h.toExpr.toSyntax -- look at `h` as syntax
      let tm ← `(term| 2 * $th) --and multipliy it by `2`
      let tme ← elabTerm tm h.type -- the "elaborated" term, that is the syntax transformed in a term of `h.type`
      liftMetaTactic fun mv => do
        let mv ← mv.define s!"double_{h.userName.toString}".toName h.type tme
        let (_, mv) ← mv.intro1P
        return [mv]

elab "succNatStx" : tactic => SuccNatStx

example (n m k : ℕ) (H : n = 3 + 1) : True := by
  succNatStx
  sorry
end elabs
