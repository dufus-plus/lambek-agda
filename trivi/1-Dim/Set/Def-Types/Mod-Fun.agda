open import 0-Dim.!quali
import 1-Dim.Graph.Def-Types.Mod-Fun as Graph
open import 1-Dim.Set.Def-Types.Mod
open import 1-Dim.Set.Def-Types-pub.Mod

module 1-Dim.Set.Def-Types.Mod-Fun where

-- function between Modules
module _ (AB : [2~] _) (2M @(M1 > M2) : [2~] [Mod] AB) where
  :Mod-Fun : Any
  :Mod-Fun = Graph.:Mod-Fun _ (M1 .It > M2 .It)

  record Mod-[Fun] : Any where
    constructor ↑
    field ↓ : :Mod-Fun
