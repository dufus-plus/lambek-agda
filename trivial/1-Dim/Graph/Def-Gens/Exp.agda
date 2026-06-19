open import 0-Dim.!quali
open import 1-Dim.Graph.Def-Types
open import 1-Dim.Graph.Def-Types-pub
import 1-Dim.AnyGraph.Def-Types as AnyGraph

module 1-Dim.Graph.Def-Gens.Exp where

module _ (AB : [2~] [Ob]) where
  Exp : [Ob] -- Graph
  Exp .El = [Fun] AB
  Exp .To = Fun-[To] _

Exp-Id : AnyGraph.Rel-[0-Fun] _ (! > Exp)
Exp-Id _ .f-el = ⑴
Exp-Id _ .f-to _ = ⑴

-- function composition on Graphs respects the *tensor* product on Graph
Exp-Mu : AnyGraph.Rel-[2T-Fun] _ ((Exp × Exp) > Exp)
Exp-Mu _ .f-el (fab × fbc) .f-el   = fab .f-el   ∘ fbc .f-el
Exp-Mu _ .f-el (fab × fbc) .f-to _ = fab .f-to _ ∘ fbc .f-to _
Exp-Mu _ .f-to _ (↑₁ (fgto × (≡ fbc))) .↓ a = fbc .f-to _ (fgto .↓ a)
Exp-Mu _ .f-to _ (↑₂ ((≡ fab) × fgto)) .↓ a = fgto .↓ (fab .f-el a)
