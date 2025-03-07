import Mathlib.Tactic



abbrev State (σ α : Type*) := σ → σ × α

instance (σ : Type*) : Monad (State σ) where
  pure a := fun s => (s, a)
  bind x f := fun s ↦
    let (s', a) := x s
    f a s'

abbrev m := State ℕ

def f : ℕ → m ℤ := by
  intro n
  intro s
  exact (n, s)

def g : ℤ → m Bool := by
  intro
  intro s
  exact (s, true)

#check (fun (a : ℕ) ↦ bind (bind (pure a) f) g)

-- let /

def firstThirdFifthSeventh (lookup : List ℕ → Nat → m ℕ) (xs : List ℕ) : m (ℕ × ℕ) :=
  -- lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (seventh)

-- def f := bind (m := State ℕ) (α := ℕ) (β := Bool)

-- def foo : State ℕ ℕ := by
--   intro n 




def Fib (n : ℕ) : ℕ :=
  match n with
 | 0 => 1
 | 1 => 1
 | k + 2 => (Fib k) + Fib (k+1)

def FibM_bad (n : ℕ) : State (List ℕ) ℕ := do
  fun L ↦ match L.get? n with
    | some y => ⟨L, y⟩ -- case when `n < L.length`
    | none => match n with -- case when `L.length ≤ n`
      | 0 => ⟨[1], 1⟩ -- subcase when `L` is empty
      | 1 => ⟨[1, 1], 1⟩ -- subcase when `L` is a singleton
      | k + 2 =>
        let sum : ℕ := ((FibM_bad k) L).2 + ((FibM_bad (k+1)) L).2
        ⟨L ++ [sum], sum⟩  -- subcase when `L` has at least two elements


-- ## From Siddhartha
-- Recall: `State' (List ℕ) ℕ := List ℕ → List ℕ × ℕ`
def FibM (n : ℕ) : State (List ℕ) ℕ := do
  fun L ↦ match L[n]? with
    | some y => ⟨L, y⟩ -- case when `n < L.length`
    | none => match n with -- case when `L.length ≤ n`
      | 0 => ⟨[1], 1⟩ -- subcase when `L` is empty
      | 1 => ⟨[1, 1], 1⟩ -- subcase when `L` is a singleton
      | k + 2 =>      -- subcase when `L` has at least two elements
        let (L', s₁) := (FibM k) L
        let (L'', s₂) := (FibM (k + 1)) L'
        let sum : ℕ := s₁ + s₂
        ⟨L'' ++ [sum], sum⟩

instance : Repr (State (List ℕ) ℕ) := ⟨fun f n ↦ instReprNat.reprPrec (f []).2 n⟩



set_option trace.profiler true in
#eval FibM 32
set_option trace.profiler true in
#eval Fib 32
-- example (n : ℕ) : Fib n = (faeFibM' n []).2 := by
--   induction' n with m hm
--   · rfl
--   · induction' m with k hk
--     · rfl
--     · rw [add_assoc]
--       have hF : Fib (k + 2) = (Fib k) + Fib (k+1) := rfl
--       have hFM : (faeFibM' (k + 2) []).2 = (faeFibM' k []).2 + (faeFibM' (k+1) []).2:= by






-- set_option trace.profiler true in
-- #eval faeFibM_old 32
