import Lean.Elab
-- import Init.Prelude
import Mathlib.Tactic
import Mathlib.Topology.Basic

set_option linter.unusedTactic false

open scoped PiNotation

open Lean Meta Elab Tactic

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

-- *Somewhat good* but **not really good...**: let's pass to true tactics.


end macros










section elabs

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


def findNat' : TacticM (List Expr) :=
-- def findNat' : TacticM (Unit) :=
  withMainContext
    do
    -- let lctx ← getLocalHyps
    let lctx ← getLCtx
    let mut nats := #[]
    for h in lctx do
      if h.type == .const ``Nat []
        then nats := nats.push h.userName
    do logInfo m!"The list of naturals found in the context is {nats}"
    return List.map (.const · []) nats.toList
    -- return List.map (fun a ↦ Expr.const a []) nats.toList

def findNat : TacticM Unit :=
  withMainContext
    do
    let lcnats ← findNat'
    let mut nats : Array Expr := #[]
    for h in lcnats do
      nats := nats.push (Lean.mkAppN (.const `HAdd.add []) #[h, mkNatLit 1])
    do logInfo m!"{nats}"

elab "findNat" : tactic => findNat

-- def SuccNat : TacticM Unit :=
--   withMainContext do
--   let lcnats ← findNat'
--   for a in lcnats do
--   /- `liftMetaTactic` gets the `mvarid` of the main goal, run the given `tactic`,
--   then set the new goals to be the resulting goal list.-/
--   liftMetaTactic fun mv => do
--   /- `mv.assertHypotheses` Convert the given goal `Ctx |- target` into `Ctx, (hs[0].userName : hs[0].type) ... |-target`.
--     It assumes `hs[i].val` has type `hs[i].type`. -/
--       let mv ← mv.define "`a".toName (.const ``Nat []) (mkNatLit 37)--(Lean.mkAppN (.const ``Nat.mul []) #[mkNatLit 2, a])
--   /-Introduce one object from the goal `mvarid`, preserving the name used in the binder.
--     Returns a pair made of the newly introduced variable and the new goal.
--     This will fail if there is nothing to introduce, *ie* when the goal
--     does not start with a `∀`, `λ` or `let`.-/
--       let (_, mv) ← mv.intro1P
--       return [mv]

def SuccNat_verbose : TacticM Unit :=
  withMainContext do
  let lcnats ← getLCtx
  for h in lcnats do
  /- `liftMetaTactic` gets the `mvarid` of the main goal, run the given `tactic`,
  then set the new goals to be the resulting goal list.-/
  if h.type == .const ``Nat [] then
    liftMetaTactic fun mv => do
  /- `mv.assertHypotheses` Convert the given goal `Ctx |- target` into `Ctx, (hs[0].userName : hs[0].type) ... |-target`.
    It assumes `hs[i].val` has type `hs[i].type`. -/
      let mv ← mv.define s!"double_{h.userName.toString}".toName (.const ``Nat []) (Lean.mkAppN (.const ``Nat.mul []) #[mkNatLit 2, h.toExpr])
  /-Introduce one object from the goal `mvarid`, preserving the name used in the binder.
    Returns a pair made of the newly introduced variable and the new goal.
    This will fail if there is nothing to introduce, *ie* when the goal
    does not start with a `∀`, `λ` or `let`.-/
      let (_, mv) ← mv.intro1P
      return [mv]

def SuccNat : TacticM Unit :=
  withMainContext do
  let lctx ← getLCtx
  for h in lctx do
  if h.type == .const ``Nat [] then
    liftMetaTactic fun mv => do
      let mv ← mv.define s!"double_{h.userName.toString}".toName (.const ``Nat [])
        (Lean.mkAppN (.const ``Nat.mul []) #[mkNatLit 2, h.toExpr])
      let (_, mv) ← mv.intro1P
      return [mv]


elab "succNat" : tactic => SuccNat

example (n m k : ℕ) (H : n = 3 + 1) : True := by
  succNat
  sorry

end elabs
