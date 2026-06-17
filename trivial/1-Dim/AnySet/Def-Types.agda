open import 0-Dim.!quali
import 1-Dim.Set.Def-Types as Set
open import 1-Dim.Set.Def-Types-pub

module 1-Dim.AnySet.Def-Types where

[Ob] = Any.[Ob]
[Fun] = Any.[Fun]

module _ (2A : [2~] [Ob]) where
  [Rel] : [Any]
  [Rel] = (2a : [Dup2] 2A) → Set.[Ob]

module _ (2A : [2~] [Ob]) (2R @(R1 > R2) : [2~] [Rel] 2A) where
  Rel-[Fun] : [Any]
  Rel-[Fun] = (2a : [Dup2] 2A) → Set.[Fun] (R1 2a > R2 2a)

module _ (A : [Ob]) ((! > R) : [!] [~] [Rel] (2~ A)) where
  Rel-[0-Fun] : [Any]
  Rel-[0-Fun] = (a : A) → Set.[0-Fun] (! ~ R (2~ a))

module _ (3A @(A ~ B ~ C) : [3~] [Ob])
    (3R @((R₁₂ × R₂₃) ~ R₁₃) : ([Rel] (A ~ B) [×] [Rel] (B ~ C)) [~] [Rel] (A ~ C)) where
  Rel-[2-Fun] : [Any]
  Rel-[2-Fun] = (3a @(a ~ b ~ c) : [Dup3] 3A) →
      Set.[2-Fun] ((R₁₂ (a ~ b) × R₂₃ (b ~ c)) > R₁₃ (a ~ c))

module _ (22A @((A11 ~ A12) ~ (A21 ~ A22)): [22~] [Ob])
         (2VF @(f1 ~ f2): Any.[Dup|R] (2~ [Fun]) 22A)
         (2HR @(R1 ~ R2): Any.[R|Dup] (2~ [Rel]) 22A) where
  [Rel|Fun] : [Any]
  [Rel|Fun] = (2a @(a1 ~ a2) : [Dup2] (A11 ~ A12)) →
    Set.[Fun] (R1 (a1 ~ a2) > R2 (f1 a1 ~ f2 a2))
