open import 0-Dim.!quali
import 1-Dim.PoSet.Def-Types.Ob as PoSet
import 1-Dim.AnySet.Def-Types as AnySet
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet
import 2-Dim.PoQuiver.Def-Types.Obj as PoQuiver

module 2-Dim.DagPoQuiver|Quiver.Def-Types.Obj where

open PoQuiver using (‼)

-- Double Quiver aka Cubical 2-Graph
module :[Obj] where
  open PoSet.[Ob]
  -- type of 0-morphisms
  :Ob = AnyPoSet.[Ob]
  module _ ($Ob : :Ob) where
    -- type of 1-morphisms
    :V-Mor = AnySet.[Rel] (2~ $Ob)
    :H-Mor = AnyPoSet.[Rel] (2~ $Ob)
    module _ (V-Mor H-Mor : :1-Mor) where
      :H-Dag = AnyPoSet.Rel-[S-Fun] (2~ H-Mor)
      -- type of 2-morphisms
      :H|V-2Mor = Any.[Rel|Rel] _ (2~ λ 2ob → V-Mor 2ob .Ob) (2~ λ 2ob → H-Mor 2ob .Ob)
      :H-Dag|V = Any.Rel|Rel-[S₁-Fun] (2~ H|V-2Mor)

record [Obj] : [Any] where
  constructor ‼
  open :[Obj]
  field Ob : :Ob
  field V-Mor : :V-Mor Ob
  field H-Mor : :H-Mor Ob
  field H|V-2Mor : :H|V-2Mor Ob V-Mor H-Mor

  -- vertical is tight, horizontal is loose
  V-Graph : PoQuiver.[Obj]
  V-Graph = ‼ Ob V-Mor
  H-Graph : PoQuiver.[Obj]
  H-Graph = ‼ Ob H-Mor
