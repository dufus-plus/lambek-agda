open import 0-Dim
import 1-Dim.PoSet.Def-Types.Ob as PoSet
open import 1-Dim.PoSet.Def-Types-pub.Ob
import 1-Dim.AnyPoSet.Defs as AnyPoSet
import 2-Dim.PoSet-Graph.Defs.Ob as PoSet-Graph

module 2-Dim.PoSet-DblGraph.Defs.Ob where

open PoSet-Graph using (‼)

-- Double Graph aka Cubical 2-Graph
module :Ob where
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
  open :Ob
  field HV-Ob : :Ob
  field V-Mor : :1-Mor HV-Ob
  field H-Mor : :1-Mor HV-Ob
  field H|V-2Mor : :2-Mor HV-Ob V-Mor H-Mor

  -- vertical is tight, horizontal is loose
  V-Graph : PoSet-Graph.[Ob]
  V-Graph = ‼ HV-Ob V-Mor
  H-Graph : PoSet-Graph.[Ob]
  H-Graph = ‼ HV-Ob H-Mor
