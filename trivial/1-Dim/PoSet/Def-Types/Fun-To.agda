open import 0-Dim
import 1-Dim.Graph.Def-Types.Fun-To as Graph
open import 1-Dim.PoSet.Def-Types.Ob
open import 1-Dim.PoSet.Def-Types.Fun

module 1-Dim.PoSet.Def-Types.Fun-To where

-- relation on functions
module _ (AB @(A > B) : [2~] [Ob]) (2f @(f1 ~ f2) : [2~] [Fun] (A > B)) where
  open [Fun]
  :Fun-To = Graph.:Fun-To _ (f1 .↓ > f2 .↓)

  record Fun-[To] : [Any] where
    constructor ↑
    field ↓ : :Fun-To
