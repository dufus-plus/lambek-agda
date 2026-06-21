open import 0-Dim.!quali
open import 2-Dim-Pre.Matr.Def-Types.Ob
import 1-Dim.PoSet.Def-Types as PoSet
open import 1-Dim.PoSet.Def-Types-pub

--
-- define enriched (Rel)ations between [Any]
--
module 2-Dim-Pre.Matr.Def-Types.PoSet where

module _ (2O : [2~] [Ob]) where
  [PoSet] : [Any]
  [PoSet] = (2ob : [Dup2] 2O) → PoSet.[Ob]

[Dup|PoSet] = Any.[Dup|R] (2~ [PoSet])
[PoSet|Dup] = Any.[R|Dup] (2~ [PoSet])

module _ {2O : [2~] [Ob]} (R : [PoSet] 2O) where
  private module ^PoSet (2ob : _) = PoSet.[Ob] (R 2ob)
  open ^PoSet public
    using ()
    renaming
      ( It to PS^It;
        El to PS^El;
        To to PS^To;
        refl to PS^refl;
        tran to PS^tran )

module _ (2O : [2~] [Ob]) (R : [PoSet] 2O) where
  PoSet-Hom-Opp : [PoSet] (swap 2O)
  PoSet-Hom-Opp 2o = R (swap 2o)
  PoSet-To-Opp : [PoSet] 2O
  PoSet-To-Opp 2o = PoSet.To-Opp (R 2o)

module _ (2A : [2~] [Ob]) (2R @(R1 > R2) : [2~] [PoSet] 2A) where
  PoSet-[Fun] : [Any]
  PoSet-[Fun] = (2a : [Dup2] 2A) → PoSet.[Fun] (R1 2a > R2 2a)

module _ (A : [Ob]) ((! > R) : [!] [~] [PoSet] (2~ A)) where
  PoSet-[0-Fun] : [Any]
  PoSet-[0-Fun] = (a : A) → R (2~ a) .El

module _ (3O @(A ~ B ~ C) : [3~] [Ob])
    (3R @((R₁₂ × R₂₃) ~ R₁₃) : ([PoSet] (A ~ B) [×] [PoSet] (B ~ C)) [~] [PoSet] (A ~ C)) where
  PoSet-[2-Fun] : [Any]
  PoSet-[2-Fun] = (3a @(a ~ b ~ c) : [Dup3] 3O) →
      PoSet.[2-Fun] ((R₁₂ (a ~ b) × R₂₃ (b ~ c)) > R₁₃ (a ~ c))

module _ (2O @(A ~ B) : [2~] [Ob])
    (2R @(R₂₁ ~ R₁₂) : [PoSet] (B ~ A) [~] [PoSet] (A ~ B)) where
  PoSet-[S-Fun] : [Any]
  PoSet-[S-Fun] = (2a @(a ~ b) : [Dup2] 2O) →
      PoSet.[Fun] (R₂₁ (b ~ a) > R₁₂ (a ~ b))

module _ (22A @((A11 ~ A12) ~ (A21 ~ A22)) : [22~] [Ob])
         (2VF @(f1 ~ f2) : [Dup|Fun] 22A)
         (2HR @(R1 ~ R2) : [PoSet|Dup] 22A) where
  [PoSet|Fun] : [Any]
  [PoSet|Fun] =
    (2a @(a1 ~ a2) : [Dup2] (A11 ~ A12)) →
    PoSet.[Fun] (R1 (a1 ~ a2) > R2 (f1 a1 ~ f2 a2))
