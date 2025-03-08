import Lean.Elab
import Mathlib.Tactic
import Mathlib.Topology.Basic

set_option linter.unusedTactic false
set_option linter.unusedVariables false

open scoped PiNotation

open Lean Meta Elab Tactic

-- # Macros
section macros

-- **§** A first example

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

-- **§** Another example

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

-- *Somewhat good* but **not really good**...  `⌘`


end macros


section Meta
section Expressions
-- ## Expressions

-- **§** We want to create the expression `1 + 2`

#check Expr.const

def oneplustwo : Expr :=
  Expr.app (.const ``Nat.succ []) (mkNatLit 2)

#eval oneplustwo
elab "one+two" : term => return oneplustwo

#check one+two
#reduce one+two

def oneplustwo' : Expr :=
  Lean.mkAppN (.const `Nat.add []) #[mkNatLit 1, mkNatLit 2]

elab "one+two'" : term => return oneplustwo'

#check one+two' -- of course we would like `1 + 2` but it is already something.
#eval one+two'

-- **§** We want to create the expression `fun x y => x + y`
def nat : Expr := Expr.const ``Nat []

#check Expr.lam

def funAdd : Expr :=
  .lam `x nat -- try replacing `nat` with `ℕ` or `Nat`
    (.lam `y nat
      (Lean.mkAppN (.const `Nat.add []) #[.bvar 1, .bvar 0])
      BinderInfo.default)
  BinderInfo.default

elab "fun_add" : term => return funAdd

#check funAdd
#check fun_add

-- **§** We want to create the expression `∀ x : Prop, x ∧ x`.
#check Expr.forallE

def forAllAnd : Expr :=
  .forallE `x (.sort 0)
    (Lean.mkAppN (.const `And []) #[.bvar 0, .bvar 0])
  BinderInfo.default

elab "for_all_and" : term => return forAllAnd

#check for_all_and
-- #eval for_all_and

-- **§** We want to create the expression `Type 6`
def T6 : Expr :=
  .sort 7

elab "type6" : term => return T6

#check T6
#reduce T6
#check type6
#reduce type6


-- ## Free variables
-- **§** We want to create the expression `∀ n : ℕ, d + n` where `d` is a free variable.
def dAddn : Expr :=
  let dfvar := Expr.fvar (FVarId.mk `d)
  Expr.forallE `n nat
    (Lean.mkAppN (.const `Nat.add []) #[dfvar, .bvar 0]) BinderInfo.default

def dAddP : Expr :=
  let dfvar := Expr.fvar (FVarId.mk `d)
  Expr.forallE `P (.sort 0)
    (Lean.mkAppN (.const `Nat.add []) #[dfvar, .bvar 0]) BinderInfo.default

elab "d+n" : term => return dAddn
elab "d+P" : term => return dAddP

#check dAddn
#reduce d+n

#check dAddP
#reduce d+P


-- `⌘`



section Monads

-- ## An example: f/Fibonacci numbers

abbrev State (σ α : Type*) := σ → σ × α

instance (σ : Type*) : Monad (State σ) where
  pure a := fun s => (s, a)
  bind x f := fun s ↦
    let (s', a) := x s
    f a s'

-- The following definition is infamously slow as values are repeatedly computed
def Fib (n : ℕ) : ℕ :=
  match n with
 | 0 => 1
 | 1 => 1
 | k + 2 => (Fib k) + Fib (k+1)

set_option trace.profiler true in
#eval Fib 32
set_option trace.profiler true in
#eval Fib 33

-- In *python*
-- >>> def fib(n, computed = {0: 0, 1: 1}):
-- ...     if n not in computed:
-- ...         computed[n] = fib(n-1, computed) + fib(n-2, computed)
-- ...     return computed[n]


-- Recall: `State (List ℕ) ℕ := List ℕ → List ℕ × ℕ`
def FibM (n : ℕ) : State (List ℕ) ℕ := do
  fun L ↦ match L[n]? with
    | some y => ⟨L, y⟩          -- case when `n < L.length`
    | none => match n with     -- case when `L.length ≤ n`
      | 0 => ⟨[1], 1⟩           -- subcase when `L` is empty
      | 1 => ⟨[1, 1], 1⟩        -- subcase when `L` is a singleton
      | k + 2 =>                -- subcase when `L` has at least two elements
        let (L₁, s₁) := (FibM k) L
        let (L₂, s₂) := (FibM (k + 1)) L₁     -- this steps relies on the previous
        let sum : ℕ := s₁ + s₂
        -- let sum : ℕ := ((FibM_bad k) L).2 + ((FibM_bad (k+1)) L).2 -- this does not work
        ⟨L₂ ++ [sum], sum⟩      -- the `List`-part of the output has been updated

#check (FibM : ℕ → State (List ℕ) ℕ)
#check (FibM : ℕ → List ℕ → List ℕ × ℕ)

instance : Repr (State (List ℕ) ℕ) := ⟨fun f n ↦ instReprNat.reprPrec (f []).2 n⟩

-- set_option trace.profiler true in
-- #eval FibM 32 -- 0.05 seconds
-- set_option trace.profiler true in
-- #eval FibM 2000 -- 0.12 seconds


end Monads


-- ## Metavariables



/- **§** We want to create a metavariable with type `ℕ`, and assign to it value `3`. -/


def var3 : MetaM Unit := do
  let mv ← mkFreshExprMVar nat
  -- mv.mvarId!.assign (mkNatLit 3) -- try `#eval show` below before and after commenting
  IO.println s!"The value of the new metavariable is {← instantiateMVars mv}"

#eval show MetaM Unit from do var3


/- **§** The `explore` "tactic" simply
  1. Looks at The main metavariable;
  2. collects the full list of local declarations in the context
  3. prints them in the InfoView. -/

elab "explore" : tactic => do
  let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
    -- This is the *target*, so the type of the main goal `T` together with the context `Γ`;
  let metavarDecl : MetavarDecl ← mvarId.getDecl
    -- This is the identifier `?m` of the main goal, whose goal is `?m.type`.
  logInfo m!"The main metavariable is \n {mvarId} and our goal is
  \n{metavarDecl.userName} : {metavarDecl.type} "
  let localContext : LocalContext := metavarDecl.lctx
  -- This is simply `Γ`
  let mut implDet := []
  let mut locDecl := []
  -- These are *mutable* empty lists, to be populated later
  for (localDecl : LocalDecl) in localContext do
    if localDecl.isImplementationDetail then
      implDet := implDet ++ [m!"(implementation detail) \n{localDecl.userName} : {localDecl.type}"]
    else
      locDecl := locDecl ++ [m!"{localDecl.userName} : {localDecl.type}"]
        -- logInfo m!"\n{localDecl.userName} : {localDecl.type}"
  logInfo m!"The full list of (local) declarations in the context is
              \n {implDet} \n and \n {locDecl}"


theorem TwoIsTwo (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
  explore
  sorry


-- `⌘`


end Expressions


section NewTactics
-- # Elaborated tactics


def Count : TacticM Unit := do
  let f : LocalContext → TacticM Unit :=
    fun lctx ↦ logInfo m!"There are {(lctx.decls.toList.length) - 1} variables in scope"
  bind (α := LocalContext) (β := Unit) (m := TacticM)
    (getLCtx : TacticM LocalContext) f


def Count' : TacticM Unit := do
  getLCtx >>= fun lctx ↦
    logInfo m!"There are {lctx.decls.toList.length - 1} variables in scope"


def Count'' : TacticM Unit := do
  let lctx ← getLCtx
  let n := lctx.decls.toList.length
  logInfo m!"There are {n - 1} variables in scope" -- this `-1`subtracts the goal as `MVar`


def ExtrFn : TacticM Unit := do
  let mut xs := #[]
  let lctx ← getLCtx
  for lh in lctx do
    if (LocalDecl.index lh) != 0 && lh.type.isForall
      then xs := xs.push lh.userName
  do logInfo m!"The list of functions in the context is {xs}"
  return -- optional

elab "count_variables" : tactic => Count
elab "count_variables'" : tactic => Count'
elab "count_variables''" : tactic => Count''
elab "show_fun" : tactic => ExtrFn


example (α β : Type) (f g : α → β) (a : α) (h : f a = g a) : True := by
  count_variables''
  count_variables'
  count_variables
  show_fun
  sorry

example (α : Type) (f g h : α → ℕ) (h : f = g ∨ g = h) : True := by
  count_variables
  show_fun
  cases h
  · count_variables
    show_fun
    sorry
  · sorry

example (α : Type) (h : ∀ f : ℕ → ℕ, f 0 = f 1) : False := by
  show_fun
  sorry

example (α : Type) (I : ℕ → Type) (x : Π (n : ℕ), I n) : False := by
  show_fun
  sorry


-- `⌘`


elab "solve" : tactic => do
    let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
    let metavarDecl : MetavarDecl ← mvarId.getDecl
    let locCtx : LocalContext := metavarDecl.lctx
    for ld in locCtx do
      if ← isDefEq ld.type metavarDecl.type then
        mvarId.assign ld.toExpr


theorem TwoIsTwo' (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
  explore
  solve

-- `⌘`


-- ## DeepMind_Induction


example (n : ℕ) : n + 1 = 1 + n := by
  induction 12
  repeat' sorry


elab "WhatsThis " n:term : tactic =>
  do
    let metavarVars ← getLCtx
    for lh in metavarVars do
      if `n == lh.userName then
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


-- `⌘`


/- ## Back to `∧`
The following tactic destructs *completely* all `p ∧ q` *hypotheses* found in the local context:
more complicated than the macro-defined `split_and` because that one *only acted on the goal*,
here we navigate all assumptions.
-/

partial def DestrAnd : TacticM Unit := withMainContext do
  for lh in ← getLCtx do -- get the context
  let eq := Expr.isAppOf lh.type ``And --checks whether `lh` coincides with `?m_1 ∧ ?m_2`
  -- let eq := Expr.isAppOfArity lh.type ``And 2 --checks whether `lh` coincides with `?m_1 ∧ ?m_2`
  if eq then  -- if yes, the code below applies `cases` on `lh`
    liftMetaTactic -- Get goal, run a tactic, add the new goals to the new the goal list
      fun goal ↦ do
      let subgoals ← MVarId.cases goal lh.fvarId --insert new subgoals in the list of goals
      let subgoalsList := subgoals.toList
      pure (List.map (fun sg ↦
          InductionSubgoal.mvarId
          (CasesSubgoal.toInductionSubgoal sg)) subgoalsList)
    DestrAnd -- finally, a recursive call (try to comment it)
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

-- ## Modifying terms

def findNat : TacticM (List LocalDecl) := withMainContext do
  let lctx ← getLCtx
  let mut nats_LocDecl := #[]
  for h in lctx do
    if h.type == .const ``Nat []
      then nats_LocDecl := nats_LocDecl.push h
  let nats_Names := nats_LocDecl.map (·.userName)
  do logInfo m!"The list of naturals found in the context is {nats_Names}"
  return nats_LocDecl.toList

def listNat : TacticM Unit := withMainContext do
  let lcnats ← findNat

elab "listNat" : tactic => listNat

example (n m k : ℕ) (H : n = 3 + 1) : True := by
  let e : ℕ := 3 --removing the `: ℕ` creates problems, actually a stronger monad is needed.
  listNat
  sorry

def DoubleNat : TacticM Unit := withMainContext do
  let lcnats ← findNat
  for h in lcnats do
  liftMetaTactic fun mv => do
    let mv ← mv.define s!"double_{h.userName.toString}".toName nat
        (Lean.mkAppN (.const `Nat.mul []) #[mkNatLit 2, h.toExpr])
  /-Introduce one object from the goal `mvarid`, preserving the name used in the binder.
    Returns a pair made of the newly introduced variable and the new goal.
    This will fail if there is nothing to introduce, *ie* when the goal
    does not start with a `∀`, `λ` or `let`.-/
      let (_, mv) ← mv.intro1P
      return [mv]

elab "doubleNat" : tactic => DoubleNat

example (n m k : ℕ) (H : n = 3 + 1) : True := by
  doubleNat
  sorry

-- The `Nat.mul 2 n` is still somewhat annoying, and this comes from our usage of expressions
-- rather than more direct syntax.

def DoubleNatStx : TacticM Unit := withMainContext do
  let lctx ← findNat
  for h in lctx do
    let th ← h.toExpr.toSyntax -- look at `h` as syntax
    let tm ← `(term| 2 * $th) --and multipliy it by `2`
    let tme ← elabTerm tm h.type -- the "elaborated" term, that is the syntax transformed in a term of `h.type`
    liftMetaTactic fun mv => do
      let mv ← mv.define s!"double_{h.userName.toString}".toName h.type tme
      let (_, mv) ← mv.intro1P
      return [mv]

elab "doubleNatStx" : tactic => DoubleNatStx

example (n m k : ℕ) (H : n = 3 + 1) : True := by
  doubleNatStx
  sorry


end NewTactics

end Meta
