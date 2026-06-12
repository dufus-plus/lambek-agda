open import 0-Dim

module 1-Dim.AnySet.Defs where

private module Set where
  open import 1-Dim.Set.Defs.Ob public
  open import 1-Dim.Set.Defs.Fun public
  open import 1-Dim.Set.Gens.Ob public
open Set.[Ob]

[Ob] = Any.[Ob]

module _ (2A : [2~] [Ob]) where
  [Rel] : [Any]
  [Rel] = [Dup2] 2A → Set.[Ob]

module _ (2A : [2~] [Ob]) (2R @(R1 > R2) : [2~] [Rel] 2A) where
  Rel-[Fun] : [Any]
  Rel-[Fun] = (2a : [Dup2] 2A) → Set.[Fun] (R1 2a > R2 2a)

module _ (A : [Ob]) ((! > R) : [!] [~] [Rel] (2~ A)) where
  Rel-[0Fun] : [Any]
  Rel-[0Fun] = (a : A) → R (2~ a) .Ob

module _ (3A @(A ~ B ~ C) : [3~] [Ob])
    (3R @((R₁₂ × R₂₃) ~ R₁₃) : ([Rel] (A ~ B) [×] [Rel] (B ~ C)) [~] [Rel] (A ~ C)) where
  Rel-[2Fun] : [Any]
  Rel-[2Fun] = (3a @(a ~ b ~ c) : [Dup3] 3A) →
      Set.[Fun] (Set.Prod (R₁₂ (a ~ b) × R₂₃ (b ~ c)) > R₁₃ (a ~ c))
