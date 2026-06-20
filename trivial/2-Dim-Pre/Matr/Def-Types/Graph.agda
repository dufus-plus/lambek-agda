open import 0-Dim.!quali
open import 2-Dim-Pre.Matr.Def-Types.Ob
import 1-Dim.Graph.Def-Types as Graph
open import 1-Dim.Graph.Def-Types-pub

--
-- define enriched (Rel)ations between [Any]
--
module 2-Dim-Pre.Matr.Def-Types.Graph where

module _ (2A : [2~] [Ob]) where
  [Graph] : [Any]
  [Graph] = [Dup2] 2A → Graph.[Ob]

module _ {2O : [2~] [Ob]} (R : [Graph] 2O) where
  private module ^Graph (2ob : _) = Graph.[Ob] (R 2ob)
  open ^Graph public
    using ()
    renaming
      ( El to G^El;
        To to G^To )

[Dup|Graph] = Any.[Dup|R] (2~ [Graph])
[Graph|Dup] = Any.[R|Dup] (2~ [Graph])

module _ (2A : [2~] [Ob]) (2R @(R1 > R2) : [2~] [Graph] 2A) where
  Graph-[Fun] : [Any]
  Graph-[Fun] = (2a : [Dup2] 2A) → Graph.[Fun] (R1 2a > R2 2a)

module _ (A : [Ob]) ((! > R) : [!] [~] [Graph] (2~ A)) where
  Graph-[0-Fun] : [Any]
  Graph-[0-Fun] = (a : A) → R (2~ a) .El

module _ (3A @(A ~ B ~ C) : [3~] [Ob])
    (((Rab × Rbc) ~ Rac) : ([Graph] (A ~ B) [×] [Graph] (B ~ C)) [~] [Graph] (A ~ C)) where
  Graph-[2P-Fun] : [Any]
  Graph-[2P-Fun] = (3a @(a ~ b ~ c) : [Dup3] 3A) →
      Graph.[2P-Fun] ((Rab (a ~ b) × Rbc (b ~ c)) > Rac (a ~ c))

module _ (3A @(A ~ B ~ C) : [3~] [Ob])
    (((Rab × Rbc) ~ Rac) : ([Graph] (A ~ B) [×] [Graph] (B ~ C)) [~] [Graph] (A ~ C)) where
  Graph-[2T-Fun] : [Any]
  Graph-[2T-Fun] = (3a @(a ~ b ~ c) : [Dup3] 3A) →
      Graph.[2T-Fun] ((Rab (a ~ b) × Rbc (b ~ c)) > Rac (a ~ c))

module _ (22A @((A11 ~ A12) ~ (A21 ~ A22)): [22~] [Ob])
         (2VF @(f1 ~ f2): Any.[Dup|R] (2~ [Fun]) 22A)
         (2HR @(R1 ~ R2): Any.[R|Dup] (2~ [Graph]) 22A) where
  [Graph|Fun] : [Any]
  [Graph|Fun] = (2a @(a1 ~ a2) : [Dup2] (A11 ~ A12)) →
    Graph.[Fun] (R1 (a1 ~ a2) > R2 (f1 a1 ~ f2 a2))
