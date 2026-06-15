open import 0-Dim-qua
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet

module 2-Dim.PoQuiver.Def-Types.Ob where

-- globular PoSet-enriched Quiver
module :[Ob] where
  module _ (Ob : AnyPoSet.[Ob]) where
    -- type of 1-morphisms
    :Hom = AnyPoSet.[Rel] (2~ Ob)
    -- 2-morphisms (equivalences) are hidden in sets

record [Ob] : [Any] where
  constructor ‼
  open :[Ob]
  field Ob  : AnyPoSet.[Ob]
  field Hom : :Hom Ob
