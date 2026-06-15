open import 0-Dim-qua
import 1-Dim.PoSet.Def-Types.Ob as PoSet
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet
import 2-Dim.PoQuiver.Def-Types.Ob as PoQuiver

module 2-Dim.DblQuiver.Def-Types.Ob where

open PoQuiver using (‼)

-- Double Quiver aka Cubical 2-Graph
module :[Ob] where
  open PoSet.[Ob]
  -- type of 0-morphisms
  :Ob = AnyPoSet.[Ob]
  module _ ($Ob : :Ob) where
    -- type of 1-morphisms
    :1-Mor = AnyPoSet.[Rel] (2~ $Ob)
    module _ (V-Mor H-Mor : :1-Mor) where
      -- type of 2-morphisms
      :2-Mor = Any.[Rel|Rel] _ (2~ λ 2ob → V-Mor 2ob .Ob) (2~ λ 2ob → H-Mor 2ob .Ob)

record [Ob] : [Any] where
  constructor ‼
  open :[Ob]
  field Ob : :Ob
  field V-Mor : :1-Mor Ob
  field H-Mor : :1-Mor Ob
  field H|V-2Mor : :2-Mor Ob V-Mor H-Mor

  -- vertical is tight, horizontal is loose
  V-Graph : PoQuiver.[Ob]
  V-Graph = ‼ Ob V-Mor
  H-Graph : PoQuiver.[Ob]
  H-Graph = ‼ Ob H-Mor
