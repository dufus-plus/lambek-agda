open import 0-Dim.!quali
open import 2-Dim-Pre.Matr.Def-Types.Ob
import 2-Dim.Cat.Def-Types as Cat
open import 2-Dim.Cat.Def-Types-pub

--
-- define enriched (Rel)ations between Any
--
module 3-Dim-Pre.2-Matr.Def-Types.Cat where

module _ (2O : [2~] [Ob]) where
  [Cat] : Any
  [Cat] = (2ob : [Dup2] 2O) → Cat.[Obj]

[Dup|Cat] = Any.[Dup|R] (2~ [Cat])
[Cat|Dup] = Any.[R|Dup] (2~ [Cat])

module _ {2O : [2~] [Ob]} (R : [Cat] 2O) where
  private module ^Cat (2ob : _) = Cat.[Obj] (R 2ob)
  open ^Cat public
    using ()
    renaming
      ( Ob to PC^Ob ) -- TODO

module _ (2O : [2~] [Ob]) (R : [Cat] 2O) where
  Cat-Hom-Opp : [Cat] (swap 2O)
  Cat-Hom-Opp 2o = R (swap 2o)
  Cat-To-Opp : [Cat] 2O
  Cat-To-Opp 2o = Cat.To-Opp (R 2o)

module _ (2A : [2~] [Ob]) (2R @(R1 > R2) : [2~] [Cat] 2A) where
  Cat-[Fun] : Any
  Cat-[Fun] = (2a : [Dup2] 2A) → Cat.[Fun] (R1 2a > R2 2a)

module _ (A : [Ob]) ((! > R) : [!] [~] [Cat] (2~ A)) where
  Cat-[0-Fun] : Any
  Cat-[0-Fun] = (a : A) → R (2~ a) .Ob

module _ (3O @(A ~ B ~ C) : [3~] [Ob])
    (3R @((R₁₂ × R₂₃) ~ R₁₃) : ([Cat] (A ~ B) [×] [Cat] (B ~ C)) [~] [Cat] (A ~ C)) where
  Cat-[2-Fun] : Any
  Cat-[2-Fun] = (3a @(a ~ b ~ c) : [Dup3] 3O) →
      Cat.[2-Fun] ((R₁₂ (a ~ b) × R₂₃ (b ~ c)) > R₁₃ (a ~ c))

module _ (2O @(A ~ B) : [2~] [Ob])
    (2R @(R₂₁ ~ R₁₂) : [Cat] (B ~ A) [~] [Cat] (A ~ B)) where
  Cat-[S-Fun] : Any
  Cat-[S-Fun] = (2a @(a ~ b) : [Dup2] 2O) →
      Cat.[Fun] (R₂₁ (b ~ a) > R₁₂ (a ~ b))

module _ (22A @((A11 ~ A12) ~ (A21 ~ A22)) : [22~] [Ob])
         (2VF @(f1 ~ f2) : [Dup|Fun] 22A)
         (2HR @(R1 ~ R2) : [Cat|Dup] 22A) where
  [Cat|Fun] : Any
  [Cat|Fun] =
    (2a @(a1 ~ a2) : [Dup2] (A11 ~ A12)) →
    Cat.[Fun] (R1 (a1 ~ a2) > R2 (f1 a1 ~ f2 a2))
