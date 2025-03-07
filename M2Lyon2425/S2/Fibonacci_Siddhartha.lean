import Mathlib.Tactic



abbrev State' (σ α : Type*) := σ → σ × α

instance (σ : Type*) : Monad (State' σ) where
  pure a := fun s => (s, a)
  bind x f := fun s ↦
    let (s', a) := x s
    f a s'


def faeFibM_old' (n : ℕ) : State' (List ℕ) ℕ := do
  fun L ↦ match L.get? n with
    | some y => ⟨L, y⟩ -- case when `n < L.length`
    | none => match n with -- case when `L.length ≤ n`
      | 0 => ⟨[1], 1⟩ -- subcase when `L` is empty
      | 1 => ⟨[1, 1], 1⟩ -- subcase when `L` is a singleton
      | k + 2 =>
        let sum : ℕ := ((faeFibM_old' k) L).2 + ((faeFibM_old' (k+1)) L).2
        ⟨L ++ [sum], sum⟩  -- subcase when `L` has at least two elements

-- ## From Siddhartha
-- Recall: `State' (List ℕ) ℕ := List ℕ → List ℕ × ℕ`
def faeFibM' (n : ℕ) : State' (List ℕ) ℕ := do
  fun L ↦ match L[n]? with
    | some y => ⟨L, y⟩ -- case when `n < L.length`
    | none => match n with -- case when `L.length ≤ n`
      | 0 => ⟨[1], 1⟩ -- subcase when `L` is empty
      | 1 => ⟨[1, 1], 1⟩ -- subcase when `L` is a singleton
      | k + 2 =>      -- subcase when `L` has at least two elements
        let (L', s₁) := (faeFibM' k) L
        let (L'', s₂) := (faeFibM' (k + 1)) L'
        let sum : ℕ := s₁ + s₂
        ⟨L'' ++ [sum], sum⟩

instance : Repr (State' (List ℕ) ℕ) := ⟨fun f n ↦ instReprNat.reprPrec (f []).2 n⟩

-- set_option trace.profiler true in
#eval faeFibM' 32
#eval faeFibM_old' 32

-- set_option trace.profiler true in
-- #eval faeFibM_old 32
