import Mathlib.CategoryTheory.Comma.StructuredArrow
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.GroupTheory.Abelianization
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Functor.Category

universe u

open CategoryTheory

namespace sandbox

/-
## Manipulation de catégories.
-/

-- Catégorie des foncteurs de `ℤ` dans la catégorie des groupes abéliens.
abbrev Comp := ℤ ⥤ AddCommGrp.{u}

/-
(Ensembles ordonnés comme catégories.)

Quelle est la structure de catégorie sur `ℤ` ?
Comment construit-on un objet de cette catégorie ?
Comment construit-on un morphisme ?
-/

/-
(Catégories concrètes.)

Qu'est-ce que la catégorie `AddCommGrp.{u}` ? Que signifie le `u` ici ?
Comment construit-on un objet de `AddCommGrp.{u}` ?
Et un morphisme ? (`AddCommGrp.ofHom`)
-/

-- Exemple d'objet de `Comp` : l'objet nul (+ exemple d'utilisation de la tactique `asesop`).

--Exercice à trous :
def Zero : Comp.{u} where
  obj _ := sorry -- Comment définit l'objet nul ? (Le groupe abélien trivial dans `Type u` s'appelle `PUnit`.)
  map _ := sorry -- Le morphisme nul dans `AddCommGrp` s'appelle `0`.
  map_id := sorry
  map_comp := sorry

/-
Définition d'un objet initial, d'un objet terminal ? Exemples dans diverses catégories (`ℤ`, `AddCommGrp`, `Type`,
la catégorie des anneaux etc).
-/

def isTerminal_zero : Limits.IsTerminal Zero := by sorry

-- Deux constructeurs, lequel vaut-il mieux utiliser ici ?
#check CategoryTheory.Limits.IsTerminal.ofUnique
#check CategoryTheory.Limits.IsTerminal.ofUniqueHom


-- Quelques foncteurs sur `Comp`.
-- Rappel : si `F` est un foncteur, on obtient son action sur les objets avec `F.obj`, et son action sur les morphismes avec `F.map`.
-- Rappel 2 : les objets de `Comp` sont des foncteurs, ses morphismes sont des `NatTrans`.

-- Le foncteur qui prend le `n`-ème objet:
@[simp]
def C (n : ℤ) : Comp ⥤ AddCommGrp.{u} where
  obj := sorry
  map := sorry
  map_id := sorry
  map_comp := sorry

-- Le foncteur qui décale un objet de `K` de `a`.
@[simp]
def Shift (a : ℤ) : Comp ⥤ Comp where
  obj K :=
   {
    obj := fun n ↦ K.obj (n + a)
    map := fun u ↦ sorry
    map_id := sorry
    map_comp := fun u v ↦ sorry
   }
  map f :=
    {
      app := fun n ↦ f.app (n + a)
      naturality := sorry
    }
  map_id := sorry
  map_comp := by sorry

-- Isomorphismes de foncteurs : `NatIso`.
-- Le constructeur le plus utile est :
#check NatIso.ofComponents


def C_shift (n a : ℤ) : Shift a ⋙ C n ≅ C (n + a) := by
  refine NatIso.ofComponents ?_ ?_
  · sorry
  · sorry

def ShiftShift (a b : ℤ) : Shift a ⋙ Shift b ≅ Shift (a + b) := by
  refine NatIso.ofComponents (fun K ↦ ?_) ?_
  · refine NatIso.ofComponents ?_ ?_
    · sorry
    · sorry
  · sorry -- Je conseille de commencer par `refine NatTrans.ext (funext (fun n ↦ ?_))`, car `ext` va trop loin.

-- Fonctions utiles :
#check eqToHom
#check eqToIso
#check eqToHom_map
#check eqToHom_naturality

/-
## Produits

Quelle est la définition catégorique du produit de deux objets ?
Exemples dans les catégories usuelles.
Comment vérifier concrètement que ce sont des produits ? Par exemple, le produit cartésien dans la catégorie `Type u`.

-/

variable (A B : Type u)

-- D'abord il faut construire le cône correspondant au produit cartésien. Il existe un type spécial pour ce genre de cône :
#check Limits.BinaryFan
#check Limits.BinaryFan.mk

@[simp]
def Cone : Limits.BinaryFan A B := by
  refine Limits.BinaryFan.mk (P := A × B) ?_ ?_   -- ici `P` est le candidat pour le produit
  · sorry
  · sorry

-- Ensuite pour prouver que c'est bien un produit, on a aussi une fonction spéciale :
#check Limits.BinaryFan.IsLimit.mk

example : Limits.IsLimit (Cone A B) := by
  refine Limits.BinaryFan.IsLimit.mk (Cone A B) ?_ ?_ ?_ ?_
  · sorry
  · sorry
  · sorry
  · sorry

end sandbox
