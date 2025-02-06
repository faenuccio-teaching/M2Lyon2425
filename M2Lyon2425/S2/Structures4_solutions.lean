import Init.Data.List.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Int.Interval


section Structures

structure OneNat where
  fst : ℕ

structure TwoNat where
  pair ::
  fst : ℕ
  snd : ℕ

structure Couple where
  left : ℕ
  right : ℕ

structure OneNatOneInt where
  fst : ℕ
  snd : ℤ

structure Mess (α β γ : Type) [Zero α] [TopologicalSpace β] [UniformSpace γ] :=--`where` or `:=`
  a : α := 0
  f : α → β → γ → γ
  cont : Continuous (f a)

-- `⌘`


-- This forgets the label and takes it back.
example (x : OneNat) : TwoNat :=
  {x with snd := x.1}

-- another syntax
example (x : OneNat) : TwoNat where
  __ := x
  snd := x.1

example (x : TwoNat) : OneNat := {x with} --without the `with` the extra-field is not thrown away

example (x : TwoNat) : OneNat where
 __ := x

example (x : OneNat) : Couple := x

example (x : OneNat) : Couple := sorry
  -- {x with left := x.1} fields missing: 'right'
--so, it does not "populate missing fields with the first available type-correct term: labels matter"

example (x : OneNat) : ℕ := sorry--{x with}

structure Mix where
  fst : ℕ
  right : ℕ

#check Mix.mk

def mix1 (x : TwoNat) (y : Couple) : Mix :=
  {x, y with}
/- remember that `x := {x.fst, x.snd}`, `y = {y.left, y.right}`
  and `Mix.mk` takes a `fst : ℕ` and `right : ℕ`: s we need to throw away `x.snd` and `y.left`-/

def mix1' (x : TwoNat) (y : Couple) : Mix where
  __ := x
  __ := y

-- the order does not really matter, it "destructs and reconstructs".
def mix2 (x : TwoNat) (y : Couple) : Mix :=
  {y, x with}


example : mix1 = mix1' := rfl

example : mix1 = mix2 := rfl

-- yet, if there are two identical fields, it is the first that is picked:
def ord (x₁ x₂ : TwoNat) : Mix := {x₁, x₂ with right := 3}

example (x₁ x₂ : TwoNat) : (ord x₁ x₂).fst = x₁.fst := sorry

example (x₁ x₂ : TwoNat) : (ord x₁ x₂).fst = x₂.fst := sorry


-- An example with structures having three terms.
structure Mix' where
  snd : ℕ
  left : ℕ

structure ThreeNat where
  fst : ℕ
  snd : ℕ
  thrd : ℕ

structure Mix₃ where
  right : ℕ
  left : ℕ
  thrd : ℕ

/- `x := {x.fst, x.right}`, `y := {y.snd, y.left}`, `z := {z.fst, z.snd, z.thrd}` and `Mix.mk` takes
a `fst : ℕ` and a `right : ℕ`: we need to throw away `x.left`, `y.left`, `z.snd` and `z.thrd`-/
example (x : Mix) (y : Mix') (z : ThreeNat) : Mix₃ :=
  {x, y, z with}

-- A final example with a `Prop`-valued field:

#check Mess.mk

def f₁ : Mess ℕ ℕ ℕ where
  f := fun a b ↦ a + b
  cont := {isOpen_preimage := fun _ _ ↦ trivial}
  -- cont := ⟨fun _ _ ↦ trivial⟩

def f₂ : Mess ℕ ℕ ℕ where
  f := fun a b ↦ a + b
  cont := continuous_of_discreteTopology

-- `Prop`-valued fields disappear by proof irrelevance
example : f₁ = f₂ := rfl


-- `⌘`


-- ## Extends


structure Blob extends OneNatOneInt, OneNat
structure Blob' extends OneNatOneInt, TwoNat

structure TwoNatExt extends OneNat where
  snd : ℕ

/- Under the hood, Lean destructs all these terms and reconstructs them "in the right order" ---
 but keeping labels. -/

-- Remember that `Couple` are pairs of left-right naturals.
def TwoExtToCouple : TwoNatExt → Couple := by --fun x ↦ {left := x.1, right := x.2} -- error! why?
  rintro ⟨x, y⟩ -- by def, `TwoNatExt` extends `OneNat`, so `x : OneNat`. So,
  exact {left := x.1, right := y}

def TwoNatToCouple : TwoNat → Couple := fun x ↦ {left := x.1, right := x.2}

-- And if there are duplicates? Remember that
-- `structure Mix where`
--   `fst : ℕ`
--   `right : ℕ`

structure ThreeNatExt extends TwoNat, Mix

#print ThreeNatExt

/- Overlapping fields are not duplicated; moreover, whenever possible, fields will coincide with
constructors of the parent structure; in case of overlapping fields, things are destructured. -/
def TwoNatToExt : TwoNat → TwoNatExt := fun x ↦ {x with}

/- In the above definition, `with` is able to
1. Destruct `x` into `x.fst` and get a `OneNat`, that populates the first field of a `TwoNatExt`
2. Observe that the other field `x.snd` has the right type and label of what is missing. -/

example (x : TwoNat) : TwoNatToExt x = ⟨⟨x.fst⟩, x.snd⟩ := rfl

/- Remember that `ThreeNatExt extends TwoNat, Mix` and
  `structure Mix where`
        `fst : ℕ`
        `right : ℕ`     -/

#check ThreeNatExt.mk

def M₁ : Mix := {fst := 17, right := 11}
def two : TwoNat := {fst := 1, snd := 2}

def three : ThreeNatExt := {M₁, two with}
def three' : ThreeNatExt := {two, M₁ with}

example : three.fst = 17 := by rfl
example : three'.fst = 1 := by rfl

/- So in reality Lean is first using the first variable (`M₁` or `two`), possibly throwing away
useless stuff, and then using what follows to complete them. -/

example : three = three' := sorry--rfl -- (they're even different, not simply not `defeq`..._
--  indeed, `three={fst = 17, snd = 2, right = 11}` while `three'={fst = 1, snd = 2, right = 11}`-/


def M₂ : Mix := {fst := 13, right := 11}
def trois : ThreeNatExt := {two, M₂ with}

example : trois.fst = 1 := rfl

example : three' = trois := rfl -- one uses `M₁`, and the other uses `M₂`.
/- both are `{fst = 1, snd = 2, right = 11}` (the field `left` has been discharged) . -/


-- `⌘`


/- ### In True Math
We can now go back to what we saw the last weeks: remember that we defined -/

class AddMonoidBad (M : Type) extends Add M, AddZeroClass M

instance : AddMonoidBad ℕ where --created using `:=` → `_` → 💡
  add := Nat.add
  zero := Nat.zero
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero

instance : AddMonoidBad ℕ := ⟨Nat.zero_add, Nat.add_zero⟩
-- instance : AddMonoidBad ℕ := ⟨Nat.add_zero, Nat.zero_add⟩ -- order matters!

instance : AddMonoidBad ℕ := {Nat.instAddMonoid with}

instance : AddMonoidBad ℕ where
  __ := Nat.instAddMonoid

end Structures

section AncillarySyntax

open scoped NNReal


-- `⌘`


def F₁ : ℝ → ℝ≥0 := fun a ↦ ‖ a ‖₊
def F₂ : ℝ → ℝ≥0 := (‖ · ‖₊)

def G₁ : ℕ → ℕ := (· + 1)
def G₂ : ℕ → ℕ := fun x ↦ x + 1
def G₃ : ℕ → ℕ := fun x ↦ Nat.succ x

example : F₁ = F₂ := rfl
example : G₁ = G₂ := rfl
example : G₂ = G₃ := rfl

def L₁ : Type _ → Type _ := (List ·) --
def L₂ : Type* → Type _ := (List ·)
def L₃ : Type* → Type* := (List ·)
/-The difference between `Type*` and `Type _` is that the first declares a term in every universe
level, the second requires Lean to infer it automatically. -/


-- `⌘`


open Real Function

def myInjective (f : ℕ → ℕ) : Prop :=
  ∀ {a b : ℕ}, f a = f b → a = b

-- def Injective (f : α → β) : Prop :=
--   ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂


lemma myInjective.comp {f g : ℕ → ℕ} (hf : myInjective f) (hg : myInjective g) :
    myInjective (f ∘ g) := by
  intro a b H
  apply hg
  apply hf
  exact H

example (f g : ℕ → ℕ) (hf : myInjective f) (hg : ∀ (a b), g a = g b → a = b) :
  myInjective (f ∘ g) := by
  apply myInjective.comp
  exact hf
  exact hg
  exact @hg

/- As "explained" in the error message, `myInjective g` creates variables `a† : ℕ` and
`b† : ℕ` so that `myInjective g` *is* `g a† = g b† → a† = b†`and the `∀` has vanished. -/

example (f g : ℕ → ℕ) (hf : Injective f) (hg : ∀ (a b), g a = g b → a = b) :
  Injective (f ∘ g) := by
  apply Injective.comp
  exact hf
  exact hg

example (a b : ℕ) (f : ℕ → ℕ) (h_myInj : myInjective f) (h_Inj : Injective f) (hab : f a = f b) :
  True := sorry
  -- have : h_myInj = h_Inj := rfl
  -- have : h_myInj = h_myInj := rfl
  -- have : h_Inj = h_Inj := rfl
  -- have : h_myInj hab = h_myInj hab := rfl
  -- have : h_myInj hab = h_Inj hab := rfl


-- `⌘`


end AncillarySyntax


noncomputable section

section Exercises

-- ## Exercise 1
open scoped NNReal
--Recall from last lecture the two classes below, and the test-variable `p`:
class NormedModuleBad (M : Type*) [AddCommGroup M] where
  norm_b : M → ℝ≥0
export NormedModuleBad (norm_b)

notation "‖" e "‖₀" => norm_b e

instance (M N : Type*) [AddCommGroup M] [AddCommGroup N] [NormedModuleBad M] [NormedModuleBad N] :
    NormedModuleBad (M × N) where
  norm_b := fun ⟨m, n⟩ ↦ max ‖m‖₀ ‖n‖₀

class ModuleWithRel (M : Type*) [AddCommGroup M] where
  rel : M → M → Prop

export ModuleWithRel (rel)

instance (M N : Type*) [AddCommGroup M] [AddCommGroup N] [ModuleWithRel M] [ModuleWithRel N] :
    ModuleWithRel (M × N) where
  rel := fun ⟨m1, n1⟩ ⟨m2, n2⟩ ↦ (rel m1 m2) ∧ (rel n1 n2)

variable (p : ∀ {T : Type}, (T → Prop) → Prop)
/- When defining a `ModuleWithRel` instance on any `NormedModuleBad` we used the relation "being in the
same ball of radius `1`". Clearly the choice of `1` was arbitrary.

Define an infinite collection of instances of `ModuleWithRel` on any `NormedModuleBad` indexed by
`ρ : ℝ≥0`, and reproduce both the bad and the good example.

There are (at least) two ways:
* Enrich the `NormedModule`'s structure with a `ρ`: this is straightforward.
* Keep `ρ` as a variable: this is much harder, both because Lean won't be very happy with a
`class` depending on a variable and because there will *really* be different instances even with
good choices, so a kind of "internal rewriting" is needed. -/

class NMB_r (M : Type) extends AddCommGroup M, NormedModuleBad M where
  ρ : ℝ≥0

instance (M : Type) [NMB_r M] : ModuleWithRel M where
  rel := fun x y ↦ ‖x - y‖₀ ≤ NMB_r.ρ M

instance (M N : Type) [NMB_r M] [NMB_r N] : NMB_r (M × N) where
  ρ := max (NMB_r.ρ M) (NMB_r.ρ N)

instance (M : Type) [NMB_r M] : ModuleWithRel M where
  rel := fun x y ↦ ‖ x - y ‖₀ ≤ NMB_r.ρ M

example (ρ : ℝ≥0) (hp : ∀ M : Type, [NMB_r M] → ∀ m : M, p (rel m))
    (M : Type) [NMB_r M] (v : M × M) : p (rel v) := by
  specialize hp (M × M) v
  -- exact hp
  sorry

class NMG_r (M : Type) extends AddCommGroup M, NormedModuleBad M where
  ρ : ℝ≥0
  rel_ρ := fun x y ↦ norm_b (x - y) ≤ ρ

instance (M : Type) [NMG_r M] : ModuleWithRel M where
  rel := NMG_r.rel_ρ--fun x y ↦ ‖x - y‖₁ ≤ NMG_r.ρ M

instance (M N : Type) [NMG_r M] [NMG_r N] : NMG_r (M × N) where
  ρ := max (NMG_r.ρ M) (NMG_r.ρ N)
  norm_b := fun ⟨m, n⟩ ↦ max ‖m‖₀ ‖n‖₀
  rel_ρ := rel

example /- (ρ : ℝ≥0) -/ (hp : ∀ M : Type, [NMG_r M] → ∀ m : M, p (rel m))
    (M : Type) [NMG_r M] (v : M × M) : p (rel v) := by
  specialize hp (M × M) v
  exact hp

-- ### The hard approach

@[nolint unusedArguments]
def aliasR (M : Type*) (ρ : ℝ≥0) [AddCommGroup M] := M

class AsAliasR (M : Type*) (ρ : ℝ≥0) [AddCommGroup M] :=
  norm_R : M → ℝ≥0
  rel_R : M → M → Prop := fun x y ↦ norm_R (x - y) ≤ ρ
  equiv : M ≃ aliasR M ρ := Equiv.refl _

instance (M M' : Type*) (ρ ρ' : ℝ≥0) [AddCommGroup M] [AddCommGroup M'] [AsAliasR M ρ]
  [AsAliasR M' ρ']: AsAliasR (M × M') (max ρ ρ') where
  norm_R := fun ⟨m₁, m₁'⟩ ↦ max (AsAliasR.norm_R ρ m₁) (AsAliasR.norm_R ρ' m₁')

instance (M : Type*) (ρ : ℝ≥0) [AddCommGroup M] : AddCommGroup (aliasR M ρ) :=
  inferInstanceAs (AddCommGroup M)

-- The `ModuleWithRel` instance on every `aliasR`.
@[nolint unusedArguments]
instance (M : Type*) (ρ : ℝ≥0) [AddCommGroup M] [AsAliasR M ρ] : ModuleWithRel (aliasR M ρ) where
  rel := @AsAliasR.rel_R M ρ _ _

variable (p : ∀ {T : Type}, (T → Prop) → Prop)

example (hp : ∀ M : Type, ∀ ρ : ℝ≥0, [AddCommGroup M] → [AsAliasR M ρ] →
    ∀ m : aliasR M ρ, p (rel m))
    (M : Type) (ρ : ℝ≥0) [AddCommGroup M] [AsAliasR M ρ] (v : aliasR (M × M) ρ) :
      p (rel (max_self ρ ▸ v)) := by
  specialize hp (M × M) (max ρ ρ) v
  convert hp
  simp only [eq_rec_constant]

-- ## Exercise 2
/- "Prove the following claims, stated in the section about the non-discrete metric on `ℕ`:
1. The uniformity is discrete if the metric is discrete.
2. As uniformities, `𝒫 (idRel) = ⊥`.
3. Is the equality `𝒫 (idRel) = ⊥` true as filters?
**ANSWER** NO
4. For any `α`, the discrete topology is the bottom element `⊥` of the type `TopologicalSpace α`.
**ANSWER** instance : CompleteLattice (TopologicalSpace α) := (gciGenerateFrom α).liftCompleteLattice"
-/
open Metric Filter Classical

example (X : Type*) [MetricSpace X] (hdisc : ∀ x y : X, x ≠ y → dist x y = 1) :
    (uniformity X) = Filter.principal (idRel : Set (X × X)) := by
  convert Metric.uniformSpace_eq_bot.mpr ?_
  · exact StrictMono.apply_eq_bot_iff fun _ _ a ↦ a
  use 1
  simp only [zero_lt_one, true_and]
  intro i j h
  exact ge_of_eq <| hdisc i j h



example (X : Type*) : (⊥ : UniformSpace X).uniformity = 𝓟 (idRel) := rfl


/- ## Exercise 3
"In the attached file `PlanMetro.pdf` you find a reduced version of Lyon's subway network. I have
already defined the type of `Stations`.

1. Find a way to formalize lines (both ordered and non-ordered), and the notion for two stations of
being connected by a path.

2. Prove that being connected is an equivalence relation.

3. Prove that if we add a "circle line" connecting all terminus', then every two stations become
connected.

4. Prove that in the above configuration with a "circle line" every trip requires of at most two
changes."
-/

inductive Stations : Type
  | JeanMace : Stations
  | SaxeGambetta : Stations
  | PlaceGuichard : Stations
  | PartDieu : Stations
  | HotelDeVille : Stations
  | CroixPacquet : Stations
  | Perrache : Stations
  | Ampere : Stations
  | Bellecour : Stations
  | Cordeliers : Stations
  | Guillotiere : Stations
  | VieuxLyon : Stations

instance : Inhabited Stations := ⟨Stations.PartDieu⟩

open Stations List Classical

inductive IsDirection : List Stations → Prop
  | c_SN : IsDirection [HotelDeVille, CroixPacquet]
  | b_SN : IsDirection [JeanMace, SaxeGambetta, PlaceGuichard, PartDieu]
  | a_SN : IsDirection [Perrache, Ampere, Bellecour, Cordeliers, HotelDeVille]
  | d_EW : IsDirection [Guillotiere, Bellecour, VieuxLyon]
  | back {L : List Stations} : IsDirection L → IsDirection L.reverse

structure Directions where
  stops : List Stations
  isDir : IsDirection stops

def Directions.reverse : Directions → Directions :=
  fun D ↦ ⟨D.stops.reverse, IsDirection.back D.isDir⟩

@[simp]
lemma Directions.reverse_eq (D : Directions) : D.reverse.1 = D.1.reverse := rfl

def A_SN : Directions where
  stops := [Perrache, Ampere, Bellecour, Cordeliers, HotelDeVille]
  isDir := IsDirection.a_SN

def A_NS : Directions where
  stops := [Perrache, Ampere, Bellecour, Cordeliers, HotelDeVille].reverse
  isDir := IsDirection.back IsDirection.a_SN

instance Directions.Setoid : Setoid Directions where
  r := fun L M ↦ L.stops = M.stops.reverse ∨ L.stops = M.stops
  iseqv := by
    constructor
    · tauto
    · intros
      rw [← reverse_eq_iff]
      tauto
    · intro _ _ _
      rintro (h1 | h1) (_ | _) <;> simp_all

def Lines := Quotient Directions.Setoid

abbrev A : Lines := Quotient.mk'' A_NS
abbrev A'' : Lines := ⟦A_NS⟧
abbrev A' : Lines := Quotient.mk'' A_SN
abbrev A''' : Lines := Quotient.mk'' A_NS

example : A = A' := by
  rw [Quotient.eq'']
  constructor
  rfl

/-
inductive IsPermitted : Prop
| (S : Stat) => IsPerm [S]
| S , M => IsPerm M=> exist D, [M.last, S] ≤ D=> IsPerm M ++ S
| the same with M.head

structure Trip where
L : List Stat
perm : IsPermittes L
-/

inductive IsPermitted : List Stations → Prop
  | no_move (S : Stations) : IsPermitted [S]
  | after_last (S : Stations) (M : List Stations)/-  (hM : M ≠ [])  -/(D : Directions) :
      IsPermitted M → (M.getLastD Stations.PartDieu /- hM -/) :: [S] <:+: D.1 → IsPermitted (M ++ [S]) -- M ++ [S] is `simp` normal form for `M.concat S`
  | before_head (S : Stations) (M : List Stations) /- (hM : M ≠ [])  -/(D : Directions) :
      IsPermitted M → S :: [M.headD Stations.PartDieu/- hM -/] <:+: D.1 → IsPermitted (S :: M)

lemma IsPermitted.ne_nil {L : List Stations} (hL : IsPermitted L) : L ≠ [] := by
  cases hL <;> simp

open IsPermitted

lemma IsPermitted_rfl (S : Stations) : IsPermitted [S] := no_move S

lemma IsPermitted_symm {L : List Stations} (hL : IsPermitted L) : IsPermitted L.reverse := by
  rcases hL with _ | ⟨S, M, D, hM, hDM⟩ | ⟨S, M, D, hM, hDM⟩
  · simpa using IsPermitted.no_move _
  · simp only [reverse_append, reverse_cons, reverse_nil, nil_append, singleton_append]
    apply before_head _ _ D.reverse
    · apply IsPermitted_symm hM
    · simp
      rwa [← List.reverse_infix, reverse_reverse, ← getLastD_eq_getLast?]
  · rw [reverse_cons/- , ← concat_eq_append -/]
    apply after_last _ _ D.reverse
    · apply IsPermitted_symm hM
    · rw [← List.reverse_infix, /- reverse_reverse, -/ getLastD_eq_getLast?]
      simp
      convert hDM

  termination_by L.length









#exit
structure Trip (start arrival : Stations) where
  stops : List Stations
  not_empty : stops ≠ []
  start : stops.head not_empty = start
  arrival : stops.getLast not_empty = arrival
  -- nodup : stops.Nodup
  connection (l : List Stations) : IsInfix l stops → l.length = 2 →
    ∃ D : Directions, IsInfix l D.stops

def Connected (S A : Stations) : Prop := Nonempty (Trip S A)

lemma Connected_symm (stat : Stations) : Connected stat stat := by
  use [stat] <;> try simp
  intro l hl _
  have := hl.length_le
  simp_all

lemma Connected_rfl {pt₁ pt₂} (h : Connected pt₁ pt₂) : Connected pt₂ pt₁ := by
  let t := choice h
  use t.stops.reverse
  · simp [t.not_empty]
  · simp [t.arrival]
  · simp [t.start]
  -- · simp [t.nodup]
  · intro l hl htwo
    replace hl := reverse_reverse _ ▸ hl.reverse
    obtain ⟨D, hD⟩ := t.connection l.reverse hl (htwo ▸ length_reverse _)
    exact ⟨D.reverse, l.reverse_reverse.symm ▸ hD.reverse⟩


lemma Connected_trans {pt₁ pt₂ pt₃} (h12 : Connected pt₁ pt₂) (h23 : Connected pt₂ pt₃) :
  Connected pt₁ pt₃ := by
  constructor
  let t12 := choice h12
  let t23 := choice h23
  use t12.stops ++ t23.stops
  · simp [t12.not_empty]
  · rw [head_append_of_ne_nil]
    exact t12.start
  · rw [getLast_append_of_ne_nil t23.not_empty]
    exact t23.arrival
  · intro l hl hltwo
    by_cases in_12 : IsInfix l t12.stops
    · sorry
    · by_cases in_23 : IsInfix l t23.stops
      · sorry
      · sorry

end Exercises
