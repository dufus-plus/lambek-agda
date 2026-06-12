open import 0-Dim
import 1-Dim.Graph.Def-Types.Mod|Fun as Graph
open import 1-Dim.PoSet.Def-Types.Ob
open import 1-Dim.PoSet.Def-Types.Fun
open import 1-Dim.PoSet.Def-Types.Mod

-- definitions of 2-(Mor)phisms in (Set)oids
module 1-Dim.PoSet.Def-Types.Mod|Fun where

-- square 2-morphisms
module _ (22A : [22~] [Ob])
         (2VF @(VF1 ~ VF2) : Any.[Dup|R] (2~ [Fun]) 22A)
         (2HR @(HR1 ~ HR2) : Any.[R|Dup] (2~ [Mod]) 22A) where
    open [Fun]; open [Mod]
    :Mod|Fun = Graph.:Mod|Fun _ (VF1 .↓ ~ VF2 .↓) (HR1 .↓ ~ HR2 .↓)

    record [Mod|Fun] : [Any] where
      constructor ↑
      field ↓ : :Mod|Fun
