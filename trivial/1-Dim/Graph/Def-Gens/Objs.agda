open import 0-Dim.!quali
open import 1-Dim.Graph.Def-Types.Ob
open import 1-Dim.Graph.Def-Types-pub.Ob

module 1-Dim.Graph.Def-Gens.Objs where

-- the initial Graph
Void : [Ob]
Void .Ob = Any.Void
Void .To (() ~ ())

-- the terminal Graph
Unit : [Ob]
Unit .Ob = Any.Unit
Unit .To _ = [!]

-- the (Opp)osite Graph
module _ (A : [Ob]) where
  Opp : [Ob]
  Opp .Ob = A .Ob
  Opp .To = Any.Rel-Op _ (- A .To)

module _ (AB @(A × B) : [Ob] [×] [Ob]) where
  Prod2 : [Ob]
  Prod2 .Ob = Any.Prod2 (A .Ob × B .Ob)
  Prod2 .To ((a1 × b1) ~ (a2 × b2)) = A .To (a1 ~ a2) [×] B .To (b1 ~ b2)

  Tens2 : [Ob]
  Tens2 .Ob = Any.Prod2 (A .Ob × B .Ob)
  Tens2 .To ((a1 × b1) ~ (a2 × b2)) =
    (A .To (a1 ~ a2) [×] [≡] _ (b1 ~ b2)) [+]
    ([≡] _ (a1 ~ a2) [×] B .To (b1 ~ b2))

module _ (AB @(A + B) : [Ob] [×] [Ob]) where
  Summ2 : [Ob]
  Summ2 .Ob = Any.Summ2 (A .Ob + B .Ob)
  Summ2 .To (↑₁ a1 ~ ↑₁ a2) = A .To (a1 ~ a2)
  Summ2 .To (↑₁ a1 ~ ↑₂ b2) = [⊥]
  Summ2 .To (↑₂ b1 ~ ↑₁ a2) = [⊥]
  Summ2 .To (↑₂ b1 ~ ↑₂ b2) = B .To (b1 ~ b2)

module _ (IA @(I > A) : [Any] [~] [Ob]) where
  Pow : [Ob]
  Pow .Ob = Any.Pow (I > A .Ob)
  Pow .To (f1 ~ f2) = Any.ProdI (I ~d λ i → A .To (f1 i ~ f2 i))

module _ (IA @(I × A) : [Any] [×] [Ob]) where
  CoPow : [Ob]
  CoPow .Ob = Any.CoPow (I , A .Ob)
  CoPow .To ((i1 , a1) ~ (i2 , a2)) = [≡] _ (i1 ~ i2) [×] A .To (a1 ~ a2)

module _ (IA @(I ~d A) : [Any] [~d] λ I → I → [Ob]) where
  ProdI : [Ob]
  ProdI .Ob = Any.ProdI (I ~d λ i → A i .Ob)
  ProdI .To (p1 ~ p2) = Any.ProdI (I ~d λ i → A i .To (p1 i ~ p2 i))

module _ (IA @(I ×d A) : [Any] [×d] λ I → I → [Ob]) where
  SummI : [Ob]
  SummI .Ob = Any.SummI (I ×d λ i → A i .Ob)
  SummI .To ((i1 ×d a1) ~ (i2 ×d a2)) =
    [≡] _ (i1 ~ i2) [×d] λ eq → SummI-To eq (a1 ~ a2) where
      SummI-To : [≡] _ (i1 ~ i2) → (A i1 .Ob [~] A i2 .Ob) → [Any]
      SummI-To (≡ i) (a1 ~ a2) = A i .To (a1 ~ a2)
