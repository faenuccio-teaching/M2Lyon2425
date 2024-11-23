import Mathlib.Tactic.Common
/-!
# Abstract Rewriting System

In mathematics, an abstract rewriting system is a pair (α, R) where:
  ∙ α is a set
  ∙ R ⊆ α × α
In this file, we let α be an arbitrary type, and we define the notion of binary relation
as well as all the other properties of abstract rewriting systems; that is: closures and
properties (confluency, normalisation, etc). 

## References

* [B. Nordström. Terminating General Recursion. BIT, 28, 1988][Nord88] -/

/-! 
## Binary relation

In type theory, we define the notion of a binary relation as a Prop-valued function `R` 
such that `R x y` if `x` and `y` are in relation through `R`.

Set-theoretically, it means that the relation we define is
  { (x, y) ∈ α × α | R x y }. -/
def BinaryRelation (α : Type) : Type := α → α → Prop

/-- We define the equality of two binary relations and make it so that `ext` can be used
    on them: R = T whenever (a, b) ∈ R iff (a, b) ∈ T. --/
@[ext]
lemma binrel_ext :
  ∀ {α : Type} {R S : BinaryRelation α}, 
    (∀ x y, R x y ↔ S x y) → R = S := by
  intros α R S h
  apply (@funext α (λ _ => α → Prop) (λ x => R x) (λ x => S x))
  intro x; ext y
  apply h

/-- The identity relation is the "diagonal" relation, relating one element to itself --/
def idRel {α : Type} : BinaryRelation α := 
  λ x y => x = y

/-- If R₁ and R₂ are two binary relations, then we define
       R₁ ∙ R₂ = { (a, c) | ∃ b, (a, b) ∈ R₁ ∧ (b, c) ∈ R₂ }.
    It is commonly called the "composition of relations", but here remark that we use a
    concatenated version of it, and hence we denote it using ∙. --/
def compRel {α : Type} (R R' : BinaryRelation α) : BinaryRelation α :=
  λ x z => ∃ y, R x y ∧ R' y z

@[inherit_doc]
infixl:70 " ∙ " => compRel

/-- If R is a binary relation, then it has an inverse relation R⁻¹, where:
       R⁻¹ = { (b, a) | (a, b) ∈ R }
    It is denoted `R⁻¹` here. --/
def invRel {α : Type} (R : BinaryRelation α) : BinaryRelation α :=
  λ x y => R y x

@[inherit_doc]
postfix:1024 "⁻¹" => invRel

/-! ## Closures !-/

/-- Set-theoretically wise, we define the reflexive closure of a relation `R` as:
                      R⁰ = R ∪ idRel
    This can be translated as a proposition as R⁰ = R ∨ idRel as follows. 
    Note that we also denote `R⁰` the reflexive closure of `R`. --/
def reflexiveClosure {α : Type} (R : BinaryRelation α) : BinaryRelation α :=
  λ x y => R x y ∨ idRel x y

@[inherit_doc]
postfix:1024 "⁰" => reflexiveClosure

/-- The transitive closure of a relation is defined by induction as:
        R₁ = R, Rᵢ₊₁ = R ∙ Rᵢ, R⁺ = ⋃ᵢ Rᵢ.
    It is denoted `R⁺`. --/
inductive transitiveClosure {α : Type} (R : BinaryRelation α) : α → α → Prop :=
  | carrier : ∀ x y, R x y → transitiveClosure R x y
  | concat  : ∀ x y z, R x y → transitiveClosure R y z → transitiveClosure R x z

@[inherit_doc]
postfix:1024 "⁺" => transitiveClosure

/-- The symmetric closure of a relation is defined as:
        Rsym = R ∪ R⁻¹. --/
def symmetricClosure {α : Type} (R: BinaryRelation α) : BinaryRelation α :=
  λ x y => (R x y) ∨ (R⁻¹ x y)

/-- Finally, we define the reflexive and transitive closure, and the reflexive, symmetric
    and transitive closure as union of the others closures. 

    The reflexive and transitive closure of `R` is denoted `R⋆`, and the reflexive,
    transitive and symmetric closure is denoted `R≡`. --/
def reflTransClosure {α : Type} (R : BinaryRelation α) : BinaryRelation α :=
  λ x y => R⁺ x y ∨ x = y

@[inherit_doc]
postfix:1024 "⋆" => reflTransClosure

def reflTransSymClosure {α : Type} (R : BinaryRelation α) : BinaryRelation α :=
  λ x y => (symmetricClosure R)⋆ x y

postfix:1024 "≡" => reflTransSymClosure

/-! ## Properties !-/

-- confluence, local confluence, diamond, church-rosser, strongly normalising, 
-- weakly normalising

/-- We say that a relation has the `diamond` property whenever the following diagram:
                                   a
                                 ↙   ↘  
                                a₀    a₁
                                 ↘   ↙  
                                   b
    holds for every a, a₀, a₁. --/
def has_diamond {α : Type} (R : BinaryRelation α) : Prop :=
  ∀ a a' a'', R a a' → R a a'' → ∃ b, R a' b ∧ R a'' b

/-- We say that a relation is `confluent` whenever its reflexive and transitive closure 
    has the diamond property. --/
def is_confluent {α : Type} (R : BinaryRelation α) : Prop :=
  has_diamond R⋆

/-- We say that a relation is `locally confluent` whenever the following diagram:
                                   a
                                 ↙   ↘  
                                a₀    a₁
                                 ↘⁎  ⁎↙  
                                   b
    holds for every a, a₀, a₁. --/
def is_locally_confluent {α : Type} (R : BinaryRelation α) : Prop :=
  ∀ a a' a'', R a a' → R a a'' → ∃ b, R⋆ a' b ∧ R⋆ a'' b

/-- Finally, we say that a relation is Church-Rosser if from any zig-zag, we can always
    converge to one element. --/
def is_church_rosser {α : Type} (R : BinaryRelation α) : Prop :=
  ∀ a a', R≡ a a' → ∃ b, R⋆ a b ∧ R⋆ a' b

/-- An element `a` is "in normal form" for a binary relation `R` if there is no `b` such
    that (a, b) ∈ R. --/
def in_normal_form {α : Type} (R : BinaryRelation α) (a : α) : Prop :=
  ¬(∃ b, R a b)

/-- An element `a` is said "normalising" for a binary relation `R` if there exists a `b`
    in normal form such that a →⋆ b. --/
def is_term_normalising {α : Type} (R : BinaryRelation α) (a : α) : Prop :=
  ∃ b, in_normal_form R b ∧ R⋆ a b

/-- A relation is said `normalising` whenever every element of α is normalising. --/
def is_normalising {α : Type} (R : BinaryRelation α) : Prop :=
  ∀ a, is_term_normalising R a

/-- We follow the strong normalisation definition of [Nord88]. It is done by first 
    defining an "accessibility" predicate `Accessible` by induction.
    This predicate states that if every `a` such that `R a b` are accessible, then
    naturally, `b` is also accessible.

    Note that this property can also be called "nœtherian induction". --/
inductive Accessible {α : Type} (R : BinaryRelation α) : α → Prop :=
  | intro : ∀ b, (∀ a, R a b → Accessible R a) → Accessible R b

/-- Then, a relation is said "strongly normalising" whenever there is no infinite sequence
    of reductions, i.e., when we can finitely reach from a term in normal form all its 
    terms it can be reduced from. --/
def is_strongly_normalizing {α : Type} (R : BinaryRelation α) : Prop :=
  ∀ a, Accessible R⁻¹ a

/-- A relation R is included in a relation S, denoted R ⊂ S, if for every (a, b) ∈ R,
    (a, b) ∈ S. --/
def is_subrelation {α : Type} (R S : BinaryRelation α) : Prop :=
  ∀ a b, R a b → S a b

@[inherit_doc]
infixl:75 " ⊂ " => is_subrelation

/-! ## Utility lemmas -/

/-! ### On concatenation of closures -/

/-- The concatenation of two elements of R⁺ is again in R⁺. --/
lemma concat_trans :
  ∀ {α : Type} {R : BinaryRelation α} {x y z : α}, 
    R⁺ x y → R⁺ y z → R⁺ x z := by
  intro α R x y z hxy hyz
  induction hxy with
  | carrier x' y' hx'y' => 
    apply transitiveClosure.concat
    · exact hx'y'
    · exact hyz
  | concat x' y' z' hx'y' _ ih =>
    apply transitiveClosure.concat
    · exact hx'y'
    · apply ih; trivial

@[inherit_doc]
infixl:70 " ∙⁺ " => concat_trans

/-- The concatenation of two elements of R⋆ is again in R⋆. --/
lemma concat_trans_refl : 
  ∀ {α : Type} {R : BinaryRelation α} {x y z : α}, 
    R⋆ x y → R⋆ y z → R⋆ x z := by
  intro α R x y z hxy hyz
  cases hxy with
  | inl hxy => cases hyz with
    | inl hyz => left; exact hxy ∙⁺ hyz
    | inr e => rw [←e]; left; trivial
  | inr e => rw [e]; trivial

@[inherit_doc]
infixl:70 " ∙⋆ " => concat_trans_refl

def toTransClosure {α : Type} {R : BinaryRelation α} {x y : α} (h : R x y) : R⁺ x y :=
  transitiveClosure.carrier x y h

def toTransReflClosure {α : Type} {R : BinaryRelation α} {x y : α} (h : R x y) : R⋆ x y :=
  Or.inl (toTransClosure h)

/-! ### Useful inclusion properties -/

/-- If (x, y) ∈ R⁺ or R⋆, then (x, y) is also in the (symmetric closure of R)⁺/⋆. --/
lemma in_trans_rel_in_sym_closure :
  ∀ {α : Type} {R : BinaryRelation α} {x y : α},
    R⁺ x y → (symmetricClosure R)⁺ x y := by
  intro α R x y hxy
  induction hxy with
  | carrier x y hxy => left; left; trivial
  | concat x y z hxy _ ih =>
    have hxy: (symmetricClosure R) x y := Or.inl hxy
    right <;> trivial

lemma in_trans_rel_in_sym_closure' :
  ∀ {α : Type} {R : BinaryRelation α} {x y : α},
    R⁺ x y → (symmetricClosure R)⁺ y x := by
  intro α R x y hxy
  induction hxy with
    | carrier x y hxy => left; right; trivial
    | concat x y z hxy _ ih => 
      have hyx: (symmetricClosure R) y x := Or.inr hxy
      have hyx: (symmetricClosure R)⁺ y x := by left; trivial
      exact ih ∙⁺ hyx

lemma in_rel_in_sym_closure :
  ∀ {α : Type} {R : BinaryRelation α} {x y : α},
    R⋆ x y → R≡ x y := by
  intro α R x y hxy; cases hxy with
  | inl h => left; apply in_trans_rel_in_sym_closure; trivial
  | inr e => right; trivial

lemma in_rel_in_sym_closure' :
  ∀ {α : Type} {R : BinaryRelation α} {x y : α},
    R⋆ x y → R≡ y x := by
  intro α R x y hxy; cases hxy with
  | inl h => left; apply in_trans_rel_in_sym_closure'; trivial
  | inr e => right; rw [e]

/-! ### On subrelations -/

/-- If R ⊂ S and a property P is true on S, then it is also true on R. --/
lemma is_subrelation_prop :
  ∀ {α : Type} {R S : BinaryRelation α} (P : α → α → Prop),
    R ⊂ S → (∀ x y, S x y → P x y) → {x y : α} → R x y → P x y := by
  intro α R S P h hS x y hR
  apply hS; apply h; trivial  

/-- For any relation R, R⁺ ⊂ (symmetricClosure R)⁺. --/
lemma is_trans_closure_is_sym_trans_closure :
  ∀ {α : Type} (R : BinaryRelation α),
    R⁺ ⊂ (symmetricClosure R)⁺ := by
  intros α R x y; apply in_trans_rel_in_sym_closure

/-- For any relation R, R⋆ ⊂ R≡. --/
lemma is_trans_refl_closure_is_sym_trans_refl_closure :
  ∀ {α : Type} (R : BinaryRelation α),
    R⋆ ⊂ R≡ := by
  intros α R x y h; cases h with
  | inl h => left; apply is_trans_closure_is_sym_trans_closure; trivial
  | inr e => rw [e]; right; rfl

/-- If R ⊂ S, then R⋆ ⊂ S⋆. -/
lemma is_subrelation_refl_trans_closure :
  ∀ {α : Type} {R S : BinaryRelation α},
    R ⊂ S → R⋆ ⊂ S⋆ := by
  intro α R S h x y h'; cases h' with
  | inl h => induction' h with x y h' x y z _ _ ih
             · left; left; apply h; trivial
             · cases ih with
               | inl ih => left; right; apply h; trivial; trivial
               | inr e => left; left; apply h; rw [←e]; trivial
  | inr e => right; trivial

/-! ## Some facts -/

/-! ### Newmann's lemma -/

/-- We start by showing Newmann's lemma: whenever a relation is both strongly normalising
    and locally confluent, it is also confluent. 

    To do so, we start by showing the following lemma on a locally-confluent relation:
      if x → a and x →⁺ b such that every reduction from x satisfy the confluency conditions,
      then there exists a c such that a →⋆ c and b →⋆ c.

    If x → b in one step, then local confluency suffices to conclude. Otherwise, we use
    the confluence condition to conclude. --/
lemma newmann_aux :
  ∀ {α : Type} {R : BinaryRelation α} {x a b : α}, 
    is_locally_confluent R → R x a → R⁺ x b 
    → (∀ c, R x c → ∀ a' a'', R⋆ c a' → R⋆ c a'' → ∃ d, R⋆ a' d ∧ R⋆ a'' d)
    → ∃ y, R⋆ a y ∧ R⋆ b y := by
  intro α R x a b hconfl hxa hxb hchild
  induction hxb with
  | carrier y z hyz => exact hconfl y a z hxa hyz
  | concat y z t hyz hzt _ => 
    have := hconfl y z a hyz hxa
    cases this with
    | intro u h' => 
      cases h' with
      | intro hzu ha'u =>
        have := hchild z hyz t u (Or.inl hzt) hzu
        cases this with
        | intro b h' =>
          exists b; constructor
          · exact ha'u ∙⋆ h'.right
          · exact h'.left

/-- Then, we can use the above lemma to factor-out the redundancies in this proof.
    It allows us to work at it "by-hand" only in the case where we have both:
      x → a' →⁺ a and x → b' →⁺ b.
    
    In this case, we use the standard proof: first get a `t` such that a' →⋆ t and
    b' →⋆ t by local confluence. Then, get `t₁` such that a →⋆ t₁ and t →⋆ t₁ by 
    confluency of a', and finally get `t₂` such that t₁ →⋆ t₂ and b →⋆ t₂ by confluency
    of b'. --/
lemma newmann : 
  ∀ {α : Type} {R : BinaryRelation α}, 
    is_strongly_normalizing R → is_locally_confluent R → is_confluent R := by
  intro α R hnorm hconfl a
  induction (hnorm a) with
  | intro x _ ih => 
    intro a' a'' hxa' hxa''
    cases hxa' with
    | inl hxa' => cases hxa'' with
      | inl hxa'' => induction hxa' with
        | carrier y z hyz => apply newmann_aux <;> trivial
        | concat y z t hyz hzt => induction hxa'' with
          | carrier y' z' hyz' =>
            have hy't := transitiveClosure.concat y' z t hyz hzt
            have := newmann_aux hconfl hyz' hy't ih
            cases this with
            | intro b h => exists b; constructor; exact h.right; exact h.left
          | concat y' z' t' hyz' hzt' => 
              have := hconfl y' z z' hyz hyz'
              cases this with
              | intro t₀ h => 
                have := ih z hyz t t₀ (Or.inl hzt) h.left
                cases this with
                | intro t₁ h' =>
                  have := ih z' hyz' t' t₁ (Or.inl hzt') (h.right ∙⋆ h'.right)
                  cases this with
                  | intro t₂ h'' => exists t₂; constructor
                                    · exact h'.left ∙⋆ h''.right
                                    · exact h''.left
      | inr e => rw [←e]; exists a'; constructor
                 · right; rfl
                 · left; trivial
    | inr e => exists a''; rw [←e]; constructor
               · trivial
               · right; rfl

/-! ### Church-Rosser theorem -/

/-- We now show the Church-Rosser theorem: a relation is confluent iff it is Church-Rosser.

    We start by showing that if a relation is confluent, then it is Church-Rosser. This proof
    is the standard one ─ by induction on the length of the derivation ↔. --/
lemma is_confluent_is_church_rosser :
  ∀ {α : Type} {R : BinaryRelation α},
    is_confluent R → is_church_rosser R := by
  intro α R hconfl a a' h
  induction h with
  | inl h => induction h with
    | carrier x y hxy => cases hxy with
      | inl h => use y; constructor
                 · left; left; trivial
                 · right; rfl
      | inr h => use x; constructor
                 · right; rfl
                 · left; left; trivial
    | concat x y z hxy hyz ih => cases hxy with
      | inl h => cases ih with
        | intro b ih => cases ih with
          | intro hyb hzb => cases hyb with
            | inl hyb => use b; constructor
                         · left; right <;> trivial
                         · trivial
            | inr e   => use y; constructor
                         · left; left; trivial
                         · rw [e]; trivial
      | inr h => cases ih with
        | intro b ih => cases ih with
          | intro hyb hzb => 
            have hyx: (R⋆) y x := Or.inl (transitiveClosure.carrier y x h)
            have := hconfl y x b hyx hyb
            cases this with
            | intro c h => use c; constructor
                           · exact h.left
                           · exact hzb ∙⋆ h.right
  | inr e => use a; rw [e]; constructor <;> right <;> rfl


/-- We now show that if a relation is Church-Rosser, then it is confluent.
    It is, in fact, trivial, as (→⋆) ⊂ (↔)⋆. --/
lemma is_church_rosser_is_confluent :
  ∀ {α : Type} {R : BinaryRelation α},
    is_church_rosser R → is_confluent R := by
  intro α R hcr x a a' hxa hxa'
  apply hcr
  have h' := by apply in_rel_in_sym_closure'; exact hxa
  have h  := by apply in_rel_in_sym_closure; exact hxa'
  exact h' ∙⋆ h

/-- The reflexive and transitive closure is an idempotent operation --/ 
lemma refl_trans_closure_is_idempotent :
  ∀ {α : Type} {R : BinaryRelation α},
    (R⋆)⋆ = R⋆ := by
  intro α R; ext x y
  constructor <;> intro hxy
  · cases hxy with
    | inl h => induction h with
      | carrier _ _ hab => trivial
      | concat a b c hab _ ih => exact hab ∙⋆ ih
    | inr e => right; trivial
  · left; left; trivial

/-- If a relation has the diamond property, then it is confluent.
    We start by showing a helper lemma stating that:
                                   x
                                 ↙   ↘*  
                                y     z
                                 ↘⁎  ↙  
                                   t -/
lemma has_diamond_is_confluent_aux :
  ∀ {α : Type} {R : BinaryRelation α},
    has_diamond R → ∀ x y z, R x y → R⋆ x z → ∃ t, R⋆ y t ∧ R z t := by
  intro α R hd x y z hxy hxz; cases hxz with
  | inl hxz => revert y; induction' hxz with x y' hxy' x y' z hxy' _ ih
               · intro y hxy; specialize hd x y y' hxy hxy'; cases hd with
                 | intro t h => exists t; constructor
                                · left; left; exact h.left
                                · exact h.right
               · intro y hxy; specialize hd x y y' hxy hxy'; cases hd with
                 | intro t h => specialize (ih t h.right); cases ih with
                   | intro u hu => exists u; constructor
                                   · cases hu.left with
                                     | inl hu => left; right; exact h.left; trivial
                                     | inr e  => rw [←e]; left; left; exact h.left
                                   · exact hu.right
  | inr e   => exists y; constructor; right; rfl; erw [←e]; trivial

/-- Then, using this auxiliary lemma, we can show the following property: --/
lemma has_diamond_is_confluent :
  ∀ {α : Type} {R : BinaryRelation α},
    has_diamond R → is_confluent R := by
  intro α R hd a a' a'' ha' ha''; cases ha' with
  | inl ha' => revert a''; induction' ha' with a a' ha' a a' a'' ha' _ ih
               · intro a'' ha''
                 have := by apply has_diamond_is_confluent_aux hd <;> trivial
                 cases this with
                 | intro t h => exists t; constructor; exact h.left; left; left; exact h.right
               · intro a₀ ha₀;
                 have := by apply has_diamond_is_confluent_aux <;> trivial
                 cases this with
                 | intro t h => specialize ih t h.left; cases ih with
                   | intro u h' => exists u; constructor
                                   · exact h'.left
                                   · cases h'.right with
                                     | inl ht => left; right; exact h.right; trivial
                                     | inr e  => left; left; rw [←e]; exact h.right
  | inr e   => exists a''; constructor; rw [←e]; trivial; right; rfl
