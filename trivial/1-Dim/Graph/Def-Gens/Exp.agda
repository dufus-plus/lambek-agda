open import 0-Dim.!quali
open import 1-Dim.Graph.Def-Types
open import 1-Dim.Graph.Def-Types-pub
import 1-Dim.AnyGraph.Def-Types as AnyGraph

module 1-Dim.Graph.Def-Gens.Exp where

module _ (AB : [2~] [Ob]) where
  Exp : [Ob] -- Graph
  Exp .El = [Fun] AB
  Exp .To = Fun-[To] _

Exp-Id : AnyGraph.Rel-[0Fun] _ (! > Exp)
Exp-Id _ .f-ob = ⑴
Exp-Id _ .f-to _ = ⑴

-- function composition on Graphs respects the *tensor* product on Graph
Exp-Mu : AnyGraph.Rel-[2Fun] _ ((Exp × Exp) > Exp)
Exp-Mu _ .f-ob (fab × fbc) .f-ob   = fab .f-ob   ∘ fbc .f-ob
Exp-Mu _ .f-ob (fab × fbc) .f-to _ = fab .f-to _ ∘ fbc .f-to _
Exp-Mu _ .f-to _ (↑₁ (fgto × (≡ fbc))) .↓ a = fbc .f-to _ (fgto .↓ a)
Exp-Mu _ .f-to _ (↑₂ ((≡ fab) × fgto)) .↓ a = fgto .↓ (fab .f-ob a)
