open import 0-Dim.!quali
import 1-Dim.AnySet.Def-Types as AnySet

module 2-Dim.Quiver.Def-Types.Ob where

-- Setoid-enriched Quiver aka Globular 2-Graph
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
