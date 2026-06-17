open import 0-Dim.!quali
open import 1-Dim.Graph.Def-Types.Ob
open import 1-Dim.Graph.Def-Types-pub.Ob

module 1-Dim.Graph.Def-Gens.Objs where

-- the initial Graph
Void : [Ob]
Void .El = Any.Void
Void .To ()

-- the terminal Graph
Unit : [Ob]
Unit .El = Any.Unit
Unit .To _ = [!]

-- the (Opp)osite Graph
module _ (A : [Ob]) where
  Opp : [Ob]
  Opp .El = A .El
  Opp .To = Any.Rel-Op _ (A .To)

module _ (AB @(A × B) : [Ob] [×] [Ob]) where
  -- direct product
  Prod2 : [Ob]
  Prod2 .El = Any.Prod2 (A .El × B .El)
  Prod2 .To ((a1 × b1) ~ (a2 × b2)) = A .To (a1 ~ a2) [×] B .To (b1 ~ b2)

  -- tensoring
  Tens2 : [Ob]
  Tens2 .El = Any.Prod2 (A .El × B .El)
  Tens2 .To ((a1 × b1) ~ (a2 × b2)) =
    (A .To (a1 ~ a2) [×] [≡] _ (b1 ~ b2)) [+]
    ([≡] _ (a1 ~ a2) [×] B .To (b1 ~ b2))

module _ (AB @(A + B) : [Ob] [×] [Ob]) where
  Summ2 : [Ob]
  Summ2 .El = Any.Summ2 (A .El + B .El)
  Summ2 .To (↑₁ a1 ~ ↑₁ a2) = A .To (a1 ~ a2)
  Summ2 .To (↑₁ a1 ~ ↑₂ b2) = [⊥]
  Summ2 .To (↑₂ b1 ~ ↑₁ a2) = [⊥]
  Summ2 .To (↑₂ b1 ~ ↑₂ b2) = B .To (b1 ~ b2)

module _ (IA @(I > A) : [Any] [~] [Ob]) where
  Pow : [Ob]
  Pow .El = Any.Pow (I > A .El)
  Pow .To (f1 ~ f2) = Any.ProdI (I ~d λ i → A .To (f1 i ~ f2 i))

module _ (IA @(I × A) : [Any] [×] [Ob]) where
  CoPow : [Ob]
  CoPow .El = Any.CoPow (I , A .El)
  CoPow .To ((i1 , a1) ~ (i2 , a2)) = [≡] _ (i1 ~ i2) [×] A .To (a1 ~ a2)

module _ (IA @(I ~d A) : [Any] [~d] λ I → I → [Ob]) where
  ProdI : [Ob]
  ProdI .El = Any.ProdI (I ~d λ i → A i .El)
  ProdI .To (p1 ~ p2) = Any.ProdI (I ~d λ i → A i .To (p1 i ~ p2 i))

module _ (IA @(I ×d A) : [Any] [×d] λ I → I → [Ob]) where
  SummI : [Ob]
  SummI .El = Any.SummI (I ×d λ i → A i .El)
  SummI .To ((i1 ×d a1) ~ (i2 ×d a2)) =
    [≡] _ (i1 ~ i2) [×d] λ eq → SummI-To eq (a1 ~ a2) where
      SummI-To : [≡] _ (i1 ~ i2) → (A i1 .El [~] A i2 .El) → [Any]
      SummI-To (≡ i) (a1 ~ a2) = A i .To (a1 ~ a2)
