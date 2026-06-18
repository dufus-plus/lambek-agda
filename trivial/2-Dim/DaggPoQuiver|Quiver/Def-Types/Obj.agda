open import 0-Dim.!quali
import 1-Dim.PoSet.Def-Types as PoSet
open import 1-Dim.PoSet.Def-Types-pub
import 1-Dim.Set.Def-Types as Set
open import 1-Dim.Set.Def-Types-pub
import 1-Dim.AnySet.Def-Types as AnySet
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet
import 2-Dim.PoQuiver.Def-Types.Obj as PoQuiver
import 2-Dim.Quiver.Def-Types.Obj as Quiver

module 2-Dim.DaggPoQuiver|Quiver.Def-Types.Obj where

open PoQuiver using (‼)
open Quiver using (‼)

-- Double Quiver aka Cubical 2-Graph
module :[Obj] where
  -- type of 0-morphisms
  :Ob = AnyPoSet.[Ob]
  module _ ($Ob : :Ob) where
    -- type of 1-morphisms
    :V-Hom = AnySet.[Rel] (2~ $Ob)
    :H-Hom = AnyPoSet.[Rel] (2~ $Ob)
    module _ (H-Hom : :H-Hom) where
      :HDagg = AnyPoSet.Rel-[S-Fun] _ (2~ H-Hom)
    module _ (V-Hom : :V-Hom) (H-Hom : :H-Hom) where
      V-El = λ 2ob → V-Hom 2ob .El
      H-El = λ 2ob → H-Hom 2ob .El
      -- type of 2-morphisms
      :H|V-Sqr = Any.[Rel|Rel] _ (2~ V-El) (2~ H-El)
      module _ (HDagg : :HDagg H-Hom) (H|V-Sqr : :H|V-Sqr) where
        HDagg-el = λ 2ob → HDagg 2ob .f-el
        :H-Dag|V = Any.Rel|Rel-[S₁-Fun] _ _ _ (2~ H|V-Sqr) (2~ HDagg-el)

record [Obj] : [Any] where
  constructor ‼
  open :[Obj]
  field Ob : :Ob
  field V-Hom : :V-Hom Ob
  field H-Hom : :H-Hom Ob
  field HDagg : :HDagg Ob H-Hom
  field H|V-Sqr : :H|V-Sqr Ob V-Hom H-Hom

  -- vertical is tight, horizontal is loose
  V-Graph : Quiver.[Obj]
  V-Graph = ‼ Ob V-Hom
  H-Graph : PoQuiver.[Obj]
  H-Graph = ‼ Ob H-Hom
  -- TODO DaggPoQuiver
