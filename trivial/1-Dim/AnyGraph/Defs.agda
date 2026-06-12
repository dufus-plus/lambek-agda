open import 0-Dim

-- define (Gra)ph-enriched (Rel)ations
module 1-Dim.AnyGraph.Defs where

private module Graph where
  open import 1-Dim.Graph.Def-Types.Ob public
  open import 1-Dim.Graph.Def-Types.Fun public
  open import 1-Dim.Graph.Gens.Objs public
open import 1-Dim.Graph.Def-Types-pub.Ob

[Ob] = Any.[Ob]

module _ (2A : [2~] [Ob]) where
  [Rel] : [Any]
  [Rel] = [Dup2] 2A → Graph.[Ob]

module _ (2A : [2~] [Ob]) (2R @(R1 > R2) : [2~] [Rel] 2A) where
  Rel-[Fun] : [Any]
  Rel-[Fun] = (2a : [Dup2] 2A) → Graph.[Fun] (R1 2a > R2 2a)

module _ (A : [Ob]) ((! > R) : [!] [~] [Rel] (2~ A)) where
  Rel-[0Fun] : [Any]
  Rel-[0Fun] = (a : A) → R (2~ a) .Ob

module _ (3A @(A ~ B ~ C) : [3~] [Ob])
    (((R₁₂ × R₂₃) ~ R₁₃) : ([Rel] (A ~ B) [×] [Rel] (B ~ C)) [~] [Rel] (A ~ C)) where
  Rel-[2Fun] : [Any]
  Rel-[2Fun] = (3a @(a ~ b ~ c) : [Dup3] 3A) →
      Graph.[Fun] (Graph.Tens2 (R₁₂ (a ~ b) × R₂₃ (b ~ c)) > R₁₃ (a ~ c))
