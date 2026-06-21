open import 0-Dim.!quali
open import 2-Dim-Pre.Matr.Def-Types.Ob
import 2-Dim.PoCat.Def-Types as PoCat
open import 2-Dim.PoCat.Def-Types-pub

--
-- define enriched (Rel)ations between [Any]
--
module 3-Dim-Pre.2-Matr.Def-Types.PoCat where

module _ (2O : [2~] [Ob]) where
  [PoCat] : [Any]
  [PoCat] = (2ob : [Dup2] 2O) → PoCat.[Obj]

[Dup|PoCat] = Any.[Dup|R] (2~ [PoCat])
[PoCat|Dup] = Any.[R|Dup] (2~ [PoCat])

module _ {2O : [2~] [Ob]} (R : [PoCat] 2O) where
  private module ^PoCat (2ob : _) = PoCat.[Obj] (R 2ob)
  open ^PoCat public
    using ()
    renaming
      ( Ob to PC^Ob ) -- TODO

module _ (2O : [2~] [Ob]) (R : [PoCat] 2O) where
  PoCat-Hom-Opp : [PoCat] (swap 2O)
  PoCat-Hom-Opp 2o = R (swap 2o)
  PoCat-To-Opp : [PoCat] 2O
  PoCat-To-Opp 2o = PoCat.To-Opp (R 2o)

module _ (2A : [2~] [Ob]) (2R @(R1 > R2) : [2~] [PoCat] 2A) where
  PoCat-[Fun] : [Any]
  PoCat-[Fun] = (2a : [Dup2] 2A) → PoCat.[Fun] (R1 2a > R2 2a)

module _ (A : [Ob]) ((! > R) : [!] [~] [PoCat] (2~ A)) where
  PoCat-[0-Fun] : [Any]
  PoCat-[0-Fun] = (a : A) → R (2~ a) .Ob

module _ (3O @(A ~ B ~ C) : [3~] [Ob])
    (3R @((R₁₂ × R₂₃) ~ R₁₃) : ([PoCat] (A ~ B) [×] [PoCat] (B ~ C)) [~] [PoCat] (A ~ C)) where
  PoCat-[2-Fun] : [Any]
  PoCat-[2-Fun] = (3a @(a ~ b ~ c) : [Dup3] 3O) →
      PoCat.[2-Fun] ((R₁₂ (a ~ b) × R₂₃ (b ~ c)) > R₁₃ (a ~ c))

module _ (2O @(A ~ B) : [2~] [Ob])
    (2R @(R₂₁ ~ R₁₂) : [PoCat] (B ~ A) [~] [PoCat] (A ~ B)) where
  PoCat-[S-Fun] : [Any]
  PoCat-[S-Fun] = (2a @(a ~ b) : [Dup2] 2O) →
      PoCat.[Fun] (R₂₁ (b ~ a) > R₁₂ (a ~ b))

module _ (22A @((A11 ~ A12) ~ (A21 ~ A22)) : [22~] [Ob])
         (2VF @(f1 ~ f2) : [Dup|Fun] 22A)
         (2HR @(R1 ~ R2) : [PoCat|Dup] 22A) where
  [PoCat|Fun] : [Any]
  [PoCat|Fun] =
    (2a @(a1 ~ a2) : [Dup2] (A11 ~ A12)) →
    PoCat.[Fun] (R1 (a1 ~ a2) > R2 (f1 a1 ~ f2 a2))
