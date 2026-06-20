open import 0-Dim.!quali
import 2-Dim-Pre.AnyGraph.Def-Types as AnyGraph
import 1-Dim.PoSet.Def-Types as PoSet
open import 1-Dim.PoSet.Def-Types-pub

module 2-Dim-Pre.AnyPoSet.Def-Types where

[Ob] = Any.[Ob]

[Fun] = Any.[Fun]
[Dup|Fun] = Any.[Dup|Fun]
[Fun|Dup] = Any.[Fun|Dup]

module _ (2O : [2~] [Ob]) where
  [Rel] : [Any]
  [Rel] = (2ob : [Dup2] 2O) → PoSet.[Ob]

[Dup|Rel] = Any.[Dup|R] (2~ [Rel])
[Rel|Dup] = Any.[R|Dup] (2~ [Rel])

module _ {2O : [2~] [Ob]} (R : [Rel] 2O) where
  $It : AnyGraph.[Rel] 2O
  $It 2ob = R 2ob .It
  $El : Any.[Rel] 2O
  $El 2ob = R 2ob .El

module _ (2A : [2~] [Ob]) (2R @(R1 > R2) : [2~] [Rel] 2A) where
  Rel-[Fun] : [Any]
  Rel-[Fun] = (2a : [Dup2] 2A) → PoSet.[Fun] (R1 2a > R2 2a)

module _ (A : [Ob]) ((! > R) : [!] [~] [Rel] (2~ A)) where
  Rel-[0-Fun] : [Any]
  Rel-[0-Fun] = (a : A) → R (2~ a) .El

module _ (3O @(A ~ B ~ C) : [3~] [Ob])
    (3R @((R₁₂ × R₂₃) ~ R₁₃) : ([Rel] (A ~ B) [×] [Rel] (B ~ C)) [~] [Rel] (A ~ C)) where
  Rel-[2-Fun] : [Any]
  Rel-[2-Fun] = (3a @(a ~ b ~ c) : [Dup3] 3O) →
      PoSet.[2-Fun] ((R₁₂ (a ~ b) × R₂₃ (b ~ c)) > R₁₃ (a ~ c))

module _ (2O @(A ~ B) : [2~] [Ob])
    (2R @(R₂₁ ~ R₁₂) : [Rel] (B ~ A) [~] [Rel] (A ~ B)) where
  Rel-[S-Fun] : [Any]
  Rel-[S-Fun] = (2a @(a ~ b) : [Dup2] 2O) →
      PoSet.[Fun] (R₂₁ (b ~ a) > R₁₂ (a ~ b))

module _ (22A @((A11 ~ A12) ~ (A21 ~ A22)) : [22~] [Ob])
         (2VF @(f1 ~ f2) : [Dup|Fun] 22A)
         (2HR @(R1 ~ R2) : [Rel|Dup] 22A) where
  [Rel|Fun] : [Any]
  [Rel|Fun] =
    (2a @(a1 ~ a2) : [Dup2] (A11 ~ A12)) →
    PoSet.[Fun] (R1 (a1 ~ a2) > R2 (f1 a1 ~ f2 a2))

--
-- square 2-module between V&H posetoids
--
module _ (22O @((A11 ~ A12) ~ (A21 ~ A22)) : [22~] [Ob])
         (2VR @(VR1 ~ VR2) : [Dup|Rel] 22O)
         (2HR @(HR1 ~ HR2) : [Rel|Dup] 22O) where

  module :[Rel|Rel] = AnyGraph.:[Rel|Rel] 22O ($It VR1 ~ $It VR2) ($It HR1 ~ $It HR2)

  record [Rel|Rel] : [Any] where
    constructor ‼
    open :[Rel|Rel]
    field Sqr : :Sqr
    field H-lact : :H-lact Sqr
    field H-ract : :H-ract Sqr
    field V-lact : :V-lact Sqr
    field V-ract : :V-ract Sqr
