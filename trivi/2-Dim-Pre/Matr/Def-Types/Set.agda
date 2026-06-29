open import 0-Dim.!quali
open import 2-Dim-Pre.Matr.Def-Types.Ob
import 1-Dim.Set.Def-Types as Set
open import 1-Dim.Set.Def-Types-pub

--
-- define enriched (Rel)ations between Any
--
module 2-Dim-Pre.Matr.Def-Types.Set where

module _ (2A : [2~] [Ob]) where
  [Set] : Any
  [Set] = (2a : [Dup2] 2A) → Set.[Ob]

[Dup|Set] = Any.[Dup|R] (2~ [Set])
[Set|Dup] = Any.[R|Dup] (2~ [Set])

module _ (2O : [2~] [Ob]) (R : [Set] 2O) where
  Set-Hom-Opp : [Set] (swap 2O)
  Set-Hom-Opp 2o = R (swap 2o)
  Set-To-Opp : [Set] 2O
  Set-To-Opp 2o = Set.To-Opp (R 2o)

module _ {2O : [2~] [Ob]} (R : [Set] 2O) where
  private module ^Set (2ob : _) = Set.[Ob] (R 2ob)
  open ^Set public
    using ()
    renaming
      ( It to S^It;
        El to S^El;
        To to S^To;
        refl to S^refl;
        symm to S^symm;
        tran to S^tran )

module _ (2A : [2~] [Ob]) (2R @(R1 > R2) : [2~] [Set] 2A) where
  Set-[Fun] : Any
  Set-[Fun] = (2a : [Dup2] 2A) → Set.[Fun] (R1 2a > R2 2a)

module _ (A : [Ob]) ((! > R) : [!] [~] [Set] (2~ A)) where
  Set-[0-Fun] : Any
  Set-[0-Fun] = (a : A) → Set.[0-Fun] (! ~ R (2~ a))

module _ (3A @(A ~ B ~ C) : [3~] [Ob])
    (3R @((R₁₂ × R₂₃) ~ R₁₃) : ([Set] (A ~ B) [×] [Set] (B ~ C)) [~] [Set] (A ~ C)) where
  Set-[2-Fun] : Any
  Set-[2-Fun] = (3a @(a ~ b ~ c) : [Dup3] 3A) →
      Set.[2-Fun] ((R₁₂ (a ~ b) × R₂₃ (b ~ c)) > R₁₃ (a ~ c))

module _ (22A @((A11 ~ A12) ~ (A21 ~ A22)): [22~] [Ob])
         (2VF @(f1 ~ f2): Any.[Dup|R] (2~ [Fun]) 22A)
         (2HR @(R1 ~ R2): Any.[R|Dup] (2~ [Set]) 22A) where
  [Set|Fun] : Any
  [Set|Fun] = (2a @(a1 ~ a2) : [Dup2] (A11 ~ A12)) →
    Set.[Fun] (R1 (a1 ~ a2) > R2 (f1 a1 ~ f2 a2))
