open import 0-Dim.!quali
import 1-Dim.PoSet.Def-Types.Ob as PoSet
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet
import 2-Dim.PoSet-Qu.Def-Types.Obj as PoSet-Qu

module 2-Dim.PoSet|PoSet-Qu.Def-Types.Obj where

open PoSet-Qu using (‼)

-- Double Quiver aka Cubical 2-Graph
module :[Obj] where
  open PoSet.[Ob]
  module _ (Ob : [Any]) where
    -- type of 1-cells
    :V-Hom = AnyPoSet.[Rel] (2~ Ob)
    :H-Hom = AnyPoSet.[Rel] (2~ Ob)
    module _ (V-Hom : :V-Hom) (H-Hom : :H-Hom) where
      module V (2ob : _) = PoSet.[Ob] (V-Hom 2ob)
      module H (2ob : _) = PoSet.[Ob] (H-Hom 2ob)
      -- type of 2-cells
      :H|V-Sqr = Any.[Rel|Rel] _ (2~ V.El) (2~ H.El)

record [Obj] : [Any] where
  constructor ‼
  open :[Obj]

  -- data:
  field Ob : [Any]
  field V-Hom : :V-Hom Ob
  field H-Hom : :H-Hom Ob
  field H|V-Sqr : :H|V-Sqr Ob V-Hom H-Hom

  -- helpers:
  private module V-Hom (2ob : _) = PoSet.[Ob] (V-Hom 2ob)
  open V-Hom public
    using ()
    renaming
    ( It   to V-Hom-It;
      El   to V-Hom-El;
      To   to V-Hom-To;
      is   to V-Hom-is;
      refl to V-Hom-refl;
      tran to V-Hom-tran )

  private module H-Hom (2ob : _) = PoSet.[Ob] (H-Hom 2ob)
  open H-Hom public
    using ()
    renaming
    ( It   to H-Hom-It;
      El   to H-Hom-El;
      To   to H-Hom-To;
      is   to H-Hom-is;
      refl to H-Hom-refl;
      tran to H-Hom-tran )

  -- vertical is tight, horizontal is loose
  V-Ob : PoSet-Qu.[Obj]
  V-Ob = ‼ Ob V-Hom
  H-Ob : PoSet-Qu.[Obj]
  H-Ob = ‼ Ob H-Hom

open [Obj] public
  using (V-Ob; H-Ob)
