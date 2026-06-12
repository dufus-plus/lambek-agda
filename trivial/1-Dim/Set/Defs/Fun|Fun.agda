open import 0-Dim
import 1-Dim.Graph.Defs.Fun|Fun as Graph
open import 1-Dim.Set.Defs.Ob
open import 1-Dim.Set.Defs.Fun

-- definitions of 2-(Mor)phisms in (Set)oids
module 1-Dim.Set.Defs.Fun|Fun where

-- square 2-morphisms
module _ (22A : [22~] [Ob]) where
  module _  (2VF @(VF1 > VF2) : Any.[Dup|R] (2~ [Fun]) 22A)
            (2HF @(HF1 ~ HF2) : Any.[R|Dup] (2~ [Fun]) 22A) where
    open [Fun]
    :Fun|Fun = Graph.:Fun|Fun _ (VF1 .↓ ~ VF2 .↓) (HF1 .↓ ~ HF2 .↓)

    record [Fun|Fun] : [Any] where
      constructor ↑
      field ↓ : :Fun|Fun
