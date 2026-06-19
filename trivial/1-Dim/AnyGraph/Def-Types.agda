open import 0-Dim.!quali

--
-- define Graph-enriched (Rel)ations between [Any]
--
module 1-Dim.AnyGraph.Def-Types where

private module Graph where
  open import 1-Dim.Graph.Def-Types public
  open import 1-Dim.Graph.Def-Gens.Objs public
open import 1-Dim.Graph.Def-Types-pub

[Ob] = Any.[Ob]
[Fun] = Any.[Fun]

module _ (2A : [2~] [Ob]) where
  [Rel] : [Any]
  [Rel] = [Dup2] 2A → Graph.[Ob]

module _ (2A : [2~] [Ob]) (2R @(R1 > R2) : [2~] [Rel] 2A) where
  Rel-[Fun] : [Any]
  Rel-[Fun] = (2a : [Dup2] 2A) → Graph.[Fun] (R1 2a > R2 2a)

module _ (A : [Ob]) ((! > R) : [!] [~] [Rel] (2~ A)) where
  Rel-[0-Fun] : [Any]
  Rel-[0-Fun] = (a : A) → R (2~ a) .El

module _ (3A @(A ~ B ~ C) : [3~] [Ob])
    (((Rab × Rbc) ~ Rac) : ([Rel] (A ~ B) [×] [Rel] (B ~ C)) [~] [Rel] (A ~ C)) where
  Rel-[2P-Fun] : [Any]
  Rel-[2P-Fun] = (3a @(a ~ b ~ c) : [Dup3] 3A) →
      Graph.[2P-Fun] ((Rab (a ~ b) × Rbc (b ~ c)) > Rac (a ~ c))

module _ (3A @(A ~ B ~ C) : [3~] [Ob])
    (((Rab × Rbc) ~ Rac) : ([Rel] (A ~ B) [×] [Rel] (B ~ C)) [~] [Rel] (A ~ C)) where
  Rel-[2T-Fun] : [Any]
  Rel-[2T-Fun] = (3a @(a ~ b ~ c) : [Dup3] 3A) →
      Graph.[2T-Fun] ((Rab (a ~ b) × Rbc (b ~ c)) > Rac (a ~ c))

module _ (22A @((A11 ~ A12) ~ (A21 ~ A22)): [22~] [Ob])
         (2VF @(f1 ~ f2): Any.[Dup|R] (2~ [Fun]) 22A)
         (2HR @(R1 ~ R2): Any.[R|Dup] (2~ [Rel]) 22A) where
  [Rel|Fun] : [Any]
  [Rel|Fun] = (2a @(a1 ~ a2) : [Dup2] (A11 ~ A12)) →
    Graph.[Fun] (R1 (a1 ~ a2) > R2 (f1 a1 ~ f2 a2))
