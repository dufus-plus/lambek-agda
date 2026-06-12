open import 0-Dim
import 1-Dim.Graph.Gens.Objs as Graph
open import 1-Dim.PoSet.Def-Types.Ob
open import 1-Dim.PoSet.Def-Types-pub.Ob

module 1-Dim.PoSet.Gens.Objs where

-- the initial PoSetoid
Void : [Ob] -- PoSet
Void .↓ = Graph.Void
Void .is .refl ()
Void .is .tran (() ~ () ~ ())

-- the terminal PoSetoid
Unit : [Ob]
Unit .↓ = Graph.Unit
Unit .is .refl _ = !
Unit .is .tran _ _ = !

-- the (Opp)osite PoSetoid
module _ (A : [Ob]) where
  Opp : [Ob]
  Opp .↓ = Graph.Opp (A .↓)
  Opp .is .refl _ = - A .refl _
  Opp .is .tran _ ((- ato21) × (- ato32)) = - A .tran _ (ato32 × ato21)

module _ (AB @(A × B) : [2×] [Ob]) where
  Prod2 : [Ob]
  Prod2 .↓ = Graph.Prod2 (A .↓ × B .↓)
  Prod2 .is .refl _ = A .refl _ × B .refl _
  Prod2 .is .tran _ ((ato12 × bto12) × (ato23 × bto23)) =
    A .tran _ (ato12 × ato23) × B .tran _ (bto12 × bto23)

module _ (AB @(A + B) : [2×] [Ob]) where
  Summ2 : [Ob]
  Summ2 .↓ = Graph.Summ2 (A .↓ + B .↓)
  Summ2 .is .refl (↑₁ _) = A .refl _
  Summ2 .is .refl (↑₂ _) = B .refl _
  Summ2 .is .tran (↑₁ _ ~ ↑₁ _ ~ ↑₁ _) = A .tran _
  Summ2 .is .tran (↑₁ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .tran (↑₁ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .tran (↑₁ _ ~ ↑₂ _ ~ ↑₂ _) ()
  Summ2 .is .tran (↑₂ _ ~ ↑₁ _ ~ ↑₁ _) ()
  Summ2 .is .tran (↑₂ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .tran (↑₂ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .tran (↑₂ _ ~ ↑₂ _ ~ ↑₂ _) = B .tran _

module _ (IA @(I > A) : [Any] [~] [Ob]) where
  Pow : [Ob]
  Pow .↓ = Graph.Pow (I > A .↓)
  Pow .is .refl _ _ = A .refl _
  Pow .is .tran _ (fto12 × fto23) i = A .tran _ (fto12 i × fto23 i)

module _ (IA @(I × A) : [Any] [×] [Ob]) where
  CoPow : [Ob]
  CoPow .↓ = Graph.CoPow (I × A .↓)
  CoPow .is .refl _ = (≡ _) × A .refl _
  CoPow .is .tran _ ((ito12 × ato12) × (ito23 × ato23)) =
    ≡.tran _ _ (ito12 × ito23) × A .tran _ (ato12 × ato23)

module _ (IA @(I ∷ A) : [Any] [∷] λ I → I → [Ob]) where
  ProdI : [Ob]
  ProdI .↓ = Graph.ProdI (I ∷ λ i → A i .↓)
  ProdI .is .refl _ i = A i .refl _
  ProdI .is .tran _ (to12 × to23) i = A i .tran _ (to12 i × to23 i)

module _ (IA @(I ∷ A) : [Any] [∷] λ I → I → [Ob]) where
  SummI : [Ob]
  SummI .↓ = Graph.SummI (I ∷ λ i → A i .↓)
  SummI .is .refl (i ∷ _) = (≡ i) ∷ A i .refl _
  SummI .is .tran _ (((≡ i) ∷ to12) × ((≡ i) ∷ to23)) = (≡ i) ∷ A i .tran _ (to12 × to23)
