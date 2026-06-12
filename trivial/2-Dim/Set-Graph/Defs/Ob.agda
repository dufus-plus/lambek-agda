open import 0-Dim
import 1-Dim.AnySet.Defs as AnySet

module 2-Dim.Set-Graph.Defs.Ob where

-- Setoid-enriched Graph aka Globular 2-Graph
module :Ob where
  module _ (Ob : AnySet.[Ob]) where
    -- type of 1-morphisms
    :Hom = AnySet.[Rel] (2~ Ob)
    -- 2-morphisms (equivalences) are hidden in sets

record [Ob] : [Any] where
  constructor ‼
  open :Ob
  field Ob  : AnySet.[Ob]
  field Hom : :Hom Ob
