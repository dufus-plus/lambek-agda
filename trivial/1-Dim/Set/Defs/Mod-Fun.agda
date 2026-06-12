open import 0-Dim
import 1-Dim.Graph.Defs.Mod-Fun as Graph
open import 1-Dim.Set.Defs.Ob
open import 1-Dim.Set.Defs.Mod

module 1-Dim.Set.Defs.Mod-Fun where

-- function between Modules
module _ (AB @(A ~ B) : [2~] [Ob]) (2M @(M1 > M2) : [2~] [Mod] (A ~ B)) where
  open [Mod]
  :Mod-Fun = Graph.:Mod-Fun _ (M1 .↓ > M2 .↓)

  record Mod-[Fun] : [Any] where
    constructor ↑
    field ↓ : :Mod-Fun
