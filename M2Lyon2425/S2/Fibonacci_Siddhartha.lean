import Mathlib.Tactic


structure faeState (σ α : Type*) where
  run : σ → α × σ

instance (σ : Type*) : Monad (faeState σ) where
  pure x := ⟨fun s => (x, s)⟩
  bind x f := ⟨fun s =>
    let (a, s') := x.run s
    (f a).run s'⟩

def faeFibM_old (n : ℕ) : faeState (List ℕ) ℕ := do
  ⟨fun L ↦ match L.get? n with
    | some y => ⟨y, L⟩ -- case when `n < L.length`
    | none => match n with -- case when `L.length ≤ n`
      | 0 => ⟨1, [1]⟩ -- subcase when `L` is empty
      | 1 => ⟨1, [1, 1]⟩ -- subcase when `L` is a singleton
      | k + 2 =>
        let sum : ℕ := ((faeFibM_old k).1 L).1 + ((faeFibM_old (k+1)).1 L).1
        ⟨sum, L ++ [sum]⟩ -- subcase when `L` has at least two elements
    ⟩

instance : Repr (faeState (List ℕ) ℕ) :=  ⟨fun L n ↦ instReprNat.reprPrec (L.1 []).1 n⟩


-- ## From Siddhartha

def faeFibM (n : ℕ) : faeState (List ℕ) ℕ := do
  ⟨fun L ↦ match L[n]? with
    | some y => ⟨y, L⟩ -- case when `n < L.length`
    | none => match n with -- case when `L.length ≤ n`
      | 0 => ⟨1, [1]⟩ -- subcase when `L` is empty
      | 1 => ⟨1, [1, 1]⟩ -- subcase when `L` is a singleton
      | k + 2 =>      -- subcase when `L` has at least two elements
        let (s₁, L') := faeFibM k |>.run L
        let (s₂, L'') := faeFibM (k + 1) |>.run L'
        let sum : ℕ := s₁ + s₂
        ⟨sum, L'' ++ [sum]⟩
    ⟩

set_option trace.profiler true in
#eval faeFibM 32

set_option trace.profiler true in
#eval faeFibM_old 32
