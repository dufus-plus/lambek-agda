open import 0-Dim
import 1-Dim.AnyPoSet.Defs as AnyPoSet

module 2-Dim.PoSet-Graph.Defs.Ob where

-- PoSet-enriched Graph aka Globular 2-Graph
module :Ob where
  module _ (Ob : AnyPoSet.[Ob]) where
    -- type of 1-morphisms
    :Hom = AnyPoSet.[Rel] (2~ Ob)
    -- 2-morphisms (equivalences) are hidden in sets

record [Ob] : [Any] where
  constructor ‼
  open :Ob
  field Ob  : AnyPoSet.[Ob]
  field Hom : :Hom Ob
