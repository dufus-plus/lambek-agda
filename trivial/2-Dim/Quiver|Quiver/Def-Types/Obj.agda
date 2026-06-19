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

  -- helper:
  private module V-Hom (2ob : [2~] Ob) = PoSet.[Ob] (Hom 2ob)
  open Hom using () renaming
    ( It to V-Hom-It;
      El to V-Hom-El;
      To to V-Hom-To;
      refl
       ) public

  -- vertical is tight, horizontal is loose
  V-Ob : PoQuiver.[Obj]
  V-Ob = ‼ Ob V-Hom
  H-Ob : PoQuiver.[Obj]
  H-Ob = ‼ Ob H-Hom

open [Obj] public
  using (V-Ob; H-Ob)
