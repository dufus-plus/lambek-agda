open import 0-Dim.!quali
import 1-Dim.Graph.Def-Gens.Objs as Graph
open import 1-Dim.PoSet.Def-Types.Ob
open import 1-Dim.PoSet.Def-Types-pub.Ob

module 1-Dim.PoSet.Def-Gens.Objs where

-- the initial PoSetoid
Void : [Ob] -- PoSet
Void .It = Graph.Void
Void .is .refl ()
Void .is .tran ()

-- the terminal PoSetoid
Unit : [Ob]
Unit .It = Graph.Unit
Unit .is .refl _ = !
Unit .is .tran _ _ = !

module _ (AB @(A × B) : [2×] [Ob]) where
  Prod2 : [Ob]
  Prod2 .It = Graph.Prod2 (A .It × B .It)
  Prod2 .is .refl _ = A .refl _ × B .refl _
  Prod2 .is .tran _ ((ato12 × bto12) × (ato23 × bto23)) =
    A .tran _ (ato12 × ato23) × B .tran _ (bto12 × bto23)

module _ (AB @(A + B) : [2×] [Ob]) where
  Summ2 : [Ob]
  Summ2 .It = Graph.Summ2 (A .It + B .It)
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

module _ (IA @(I > A) : Any [~] [Ob]) where
  Pow : [Ob]
  Pow .It = Graph.Pow (I > A .It)
  Pow .is .refl _ _ = A .refl _
  Pow .is .tran _ (fto12 × fto23) i = A .tran _ (fto12 i × fto23 i)

module _ (IA @(I × A) : Any [×] [Ob]) where
  CoPow : [Ob]
  CoPow .It = Graph.CoPow (I × A .It)
  CoPow .is .refl _ = (≡ _) × A .refl _
  CoPow .is .tran _ ((ito12 × ato12) × (ito23 × ato23)) =
    ≡.tran (ito12 × ito23) × A .tran _ (ato12 × ato23)

module _ (IA @(I ~d A) : Any [~d] λ I → I → [Ob]) where
  ProdI : [Ob]
  ProdI .It = Graph.ProdI (I ~d λ i → A i .It)
  ProdI .is .refl _ i = A i .refl _
  ProdI .is .tran _ (to12 × to23) i = A i .tran _ (to12 i × to23 i)

module _ (IA @(I ×d A) : Any [×d] λ I → I → [Ob]) where
  SummI : [Ob]
  SummI .It = Graph.SummI (I ×d λ i → A i .It)
  SummI .is .refl (i ×d _) = (≡ i) ×d A i .refl _
  SummI .is .tran _ (((≡ i) ×d to12) × ((≡ i) ×d to23)) =
    (≡ i) ×d A i .tran _ (to12 × to23)
