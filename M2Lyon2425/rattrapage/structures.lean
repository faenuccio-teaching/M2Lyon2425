import Mathlib.Topology.Instances.Real

-- Définir la classe `TopGrp` des groupes additifs topologiques étendant
-- les classes `AddGroup` et `TopologicalSpace`

-- Créer une instance de `TopGrp` pour `ℝ`
-- instance : TopGrp ℝ

-- Créer une instance de `TopGrp` pour `ℤ`
-- instance : TopGrp ℤ where

-- Etant données `(X Y : Type*) [TopGrp X] [TopGrp Y]`, créer une instance de `TopGrp (X × Y)`

-- Etant données `(X Y : Type*) [TopGrp X] [TopGrp Y] [T1Space Y] (f : X →+ Y) (hf : Continuous f)`,
-- Montrer que `IsClosed (AddMonoidHom.ker f : Set X)`

