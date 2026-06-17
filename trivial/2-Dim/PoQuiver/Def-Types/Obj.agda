open import 0-Dim.!quali
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet

module 2-Dim.PoQuiver.Def-Types.Obj where

-- globular PoSet-enriched Quiver
module :[Obj] where
  module _ (Ob : AnyPoSet.[Ob]) where
    -- type of 1-morphisms
    :Hom = AnyPoSet.[Rel] (2~ Ob)
    -- 2-morphisms (equivalences) are hidden in sets

record [Obj] : [Any] where
  constructor ‼
  open :[Obj]
  field Ob  : AnyPoSet.[Ob]
  field Hom : :Hom Ob
