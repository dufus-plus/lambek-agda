open import 0-Dim
import 1-Dim.Graph.Gens.Ob as Graph
open import 1-Dim.Set.Defs.Ob

module 1-Dim.Set.Gens.Ob where

open [is]
open [Ob]

-- the initial Setoid
Void-Set : [is] Graph.Void
Void-Set .refl ()
Void-Set .symm (() ~ ())
Void-Set .tran (() ~ () ~ ())

Void : [Ob]
Void = ‼ _ Void-Set

-- the terminal Setoid
Unit-Set : [is] Graph.Unit
Unit-Set .refl _ = !
Unit-Set .symm _ _ = !
Unit-Set .tran _ _ = !

Unit : [Ob]
Unit = ‼ _ Unit-Set

-- the (Opp)osite Setoid
module _ (A : [Ob]) where
  Op-Set : [is] (Graph.Op (A .↓))
  Op-Set .refl _ = - A .refl _
  Op-Set .symm _ (- - ato12) = - A .symm _ (- ato12)
  Op-Set .tran _ ((- ato21) × (- ato32)) = - A .tran _ (ato32 × ato21)

  Op : [Ob]
  Op = ‼ _ Op-Set

module _ (AB @(A × B) : [Ob] [×] [Ob]) where
  Prod-Set : [is] (Graph.Prod (A .↓ × B .↓))
  Prod-Set .refl _ = A .refl _ × B .refl _
  Prod-Set .symm _ (- (ato12 × bto12)) = A .symm _ (- ato12) × B .symm _ (- bto12)
  Prod-Set .tran _ ((ato12 × bto12) × (ato23 × bto23)) =
    A .tran _ (ato12 × ato23) × B .tran _ (bto12 × bto23)

  Prod : [Ob]
  Prod = ‼ _ Prod-Set

module _ (AB @(A + B) : [Ob] [×] [Ob]) where
  Summ-Set : [is] (Graph.Summ (A .↓ + B .↓))
  Summ-Set .refl (↑₁ a1) = A .refl a1
  Summ-Set .refl (↑₂ b1) = B .refl b1
  Summ-Set .symm (↑₁ a2 ~ ↑₁ a1) (- ato21) = A .symm (a2 ~ a1) (- ato21)
  Summ-Set .symm (↑₁ a2 ~ ↑₂ b1) ()
  Summ-Set .symm (↑₂ b2 ~ ↑₁ a1) ()
  Summ-Set .symm (↑₂ b2 ~ ↑₂ b1) (- bto21) = B .symm (b2 ~ b1) (- bto21)
  Summ-Set .tran (↑₁ a1 ~ ↑₁ a2 ~ ↑₁ a3) (to12 × to23) = A .tran (a1 ~ a2 ~ a3) (to12 × to23)
  Summ-Set .tran (↑₁ a1 ~ ↑₁ a2 ~ ↑₂ b3) (to12 × ())
  Summ-Set .tran (↑₁ a1 ~ ↑₂ b2 ~ ↑₁ a3) (() × ())
  Summ-Set .tran (↑₁ a1 ~ ↑₂ b2 ~ ↑₂ b3) (() × to23)
  Summ-Set .tran (↑₂ b1 ~ ↑₁ a2 ~ ↑₁ a3) (() × to23)
  Summ-Set .tran (↑₂ b1 ~ ↑₁ a2 ~ ↑₂ b3) (() × ())
  Summ-Set .tran (↑₂ b1 ~ ↑₂ b2 ~ ↑₁ a3) (to12 × ())
  Summ-Set .tran (↑₂ b1 ~ ↑₂ b2 ~ ↑₂ b3) (to12 × to23) = B .tran (b1 ~ b2 ~ b3) (to12 × to23)

  Summ : [Ob]
  Summ = ‼ _ Summ-Set
