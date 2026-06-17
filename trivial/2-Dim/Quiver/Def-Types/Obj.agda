open import 0-Dim.!quali
import 1-Dim.AnySet.Def-Types as AnySet

module 2-Dim.Quiver.Def-Types.Obj where

-- Setoid-enriched Quiver aka Globular 2-Graph
module :[Obj] where
  :Ob = AnySet.[Ob]
  module _ (Ob : :Ob) where
    -- type of 1-morphisms
    :Hom = AnySet.[Rel] (2~ Ob)
    -- 2-morphisms (equivalences) are hidden in sets

record [Obj] : [Any] where
  constructor ‼
  open :[Obj]
  field Ob  : :Ob
  field Hom : :Hom Ob
