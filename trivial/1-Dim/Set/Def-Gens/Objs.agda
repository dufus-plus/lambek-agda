open import 0-Dim.!quali
import 1-Dim.Graph.Def-Gens.Objs as Graph
open import 1-Dim.Set.Def-Types.Ob
open import 1-Dim.Set.Def-Types-pub.Ob

module 1-Dim.Set.Def-Gens.Objs where

-- the initial Setoid
Void : [Ob]
Void .It = Graph.Void
Void .is .refl ()
Void .is .symm ()
Void .is .tran ()


-- the terminal Setoid
Unit : [Ob]
Unit .It = Graph.Unit
Unit .is .refl _ = !
Unit .is .symm _ _ = !
Unit .is .tran _ _ = !


-- the (Opp)osite Setoid
module _ (A : [Ob]) where
  Opp : [Ob]
  Opp .It = Graph.Opp (A .It)
  Opp .is .refl _ = A .refl _
  Opp .is .symm _ (ato12) = A .symm _ (ato12)
  Opp .is .tran _ ((ato21) × (ato32)) = A .tran _ (ato32 × ato21)

module _ (AB @(A × B) : [Ob] [×] [Ob]) where
  Prod2 : [Ob]
  Prod2 .It = Graph.Prod2 (A .It × B .It)
  Prod2 .is .refl _ = A .refl _ × B .refl _
  Prod2 .is .symm _ ((ato12 × bto12)) = A .symm _ (ato12) × B .symm _ (bto12)
  Prod2 .is .tran _ ((ato12 × bto12) × (ato23 × bto23)) =
    A .tran _ (ato12 × ato23) × B .tran _ (bto12 × bto23)

module _ (AB @(A + B) : [Ob] [×] [Ob]) where
  Summ2 : [Ob]
  Summ2 .It = Graph.Summ2 (A .It + B .It)
  Summ2 .is .refl (↑₁ _) = A .refl _
  Summ2 .is .refl (↑₂ _) = B .refl _
  Summ2 .is .symm (↑₁ _ ~ ↑₁ _) (ato21) = A .symm _ (ato21)
  Summ2 .is .symm (↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .symm (↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .symm (↑₂ _ ~ ↑₂ _) (bto21) = B .symm _ (bto21)
  Summ2 .is .tran (↑₁ _ ~ ↑₁ _ ~ ↑₁ _) 2to = A .tran _ 2to
  Summ2 .is .tran (↑₁ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .tran (↑₁ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .tran (↑₁ _ ~ ↑₂ _ ~ ↑₂ _) ()
  Summ2 .is .tran (↑₂ _ ~ ↑₁ _ ~ ↑₁ _) ()
  Summ2 .is .tran (↑₂ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .tran (↑₂ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .tran (↑₂ _ ~ ↑₂ _ ~ ↑₂ _) 2to = B .tran _ 2to
