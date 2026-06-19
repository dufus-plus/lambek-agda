open import 0-Dim.!quali
import 1-Dim.PoSet.Def-Types.Ob as PoSet
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet
import 2-Dim.PoQuiver.Def-Types.Obj as PoQuiver

module 2-Dim.PoQuiver|PoQuiver.Def-Types.Obj where

open PoQuiver using (‼)

-- Double Quiver aka Cubical 2-Graph
module :[Obj] where
  open PoSet.[Ob]
  -- type of 0-morphisms
  :Ob = AnyPoSet.[Ob]
  module _ (Ob : :Ob) where
    -- type of 1-morphisms
    :V-Hom = AnyPoSet.[Rel] (2~ Ob)
    :H-Hom = AnyPoSet.[Rel] (2~ Ob)
    module _ (V-Hom : :V-Hom) (H-Hom : :H-Hom) where
      module V = PoSet.[Ob] (V-Hom 2ob)
      module H = PoSet.[Ob] (H-Hom 2ob)
      -- type of 2-morphisms
      :H|V-Sqr = Any.[Rel|Rel] _ (2~ =V-El) (2~ =H-El)

record [Obj] : [Any] where
  constructor ‼
  open :[Obj]
  field Ob : :Ob
  field V-Hom : :V-Hom Ob
  field H-Hom : :H-Hom Ob
  field H|V-Sqr : :H|V-Sqr Ob V-Hom H-Hom

  V-El : Any.[Rel] (2~ Ob)
  V-El = =V-El Ob V-Hom H-Hom
  H-El : Any.[Rel] (2~ Ob)
  H-El = =H-El Ob V-Hom H-Hom

  -- vertical is tight, horizontal is loose
  V:PQ : PoQuiver.[Obj]
  V:PQ = ‼ Ob V-Hom
  H:PQ : PoQuiver.[Obj]
  H:PQ = ‼ Ob H-Hom

open [Obj] public
  using (V-El; H-El; V:PQ; H:PQ)
