open import 0-Dim.!quali
import 1-Dim.Set.Def-Types as Set
open import 1-Dim.Set.Def-Types-pub
import 1-Dim.PoSet.Def-Types as PoSet
open import 1-Dim.PoSet.Def-Types-pub
import 2-Dim-Pre.Matr.Def-Types as Matr
open import 2-Dim-Pre.Matr.Def-Types-pub
import 2-Dim-Pre.DaggPoSet-Qu.Def-Types.Obj as DaggPoSet-Qu
import 2-Dim-Pre.Set-Qu.Def-Types.Obj as Set-Qu

module 2-Dim-Pre.DaggPoSet|Set-Qu.Def-Types.Obj where

open DaggPoSet-Qu using (‼)
open Set-Qu using (‼)

--
-- Double Quiver aka Cubical 2-Graph:
-- the Carrier for Double 1-Categories
--
module :[Obj] where
  open PoSet.[Ob]
  module _ (Ob : [Any]) where
    -- type of 1-cells
    :H-Hom = Matr.[PoSet] (2~ Ob)
    :V-Hom = Matr.[Set] (2~ Ob)
    module _ (H-Hom : :H-Hom) where
      :H-Dagg = Matr.PoSet-[S-Fun] _ (2~ H-Hom)
    module _ (H-Hom : :H-Hom) (V-Hom : :V-Hom) where
      -- type of 2-cells as 2-module
      :H|V = Matr.[PoSet|Set] _ (2~ V-Hom) (2~ H-Hom)

      module _ (H-Dagg : :H-Dagg H-Hom) (H|V : :H|V) where
        :H-Dagg|V =
          (22ob @((ob11 ~ ob12) ~ (ob21 ~ ob22)): [22~] Ob) →
          (2v @(v1 ~ v2) :
                (V-Hom (ob11 ~ ob21) .El) [~] (V-Hom (ob12 ~ ob22) .El)) →
          (2h @(h1 ~ h2) :
                (H-Hom (ob11 ~ ob12) .El) [~] (H-Hom (ob21 ~ ob22) .El)) →
          (2hv : H|V .Sqr _ (v1 ~ v2) (h1 ~ h2) ) →
                H|V .Sqr _ (v2 ~ v1) (H-Dagg _ .f-el h1 ~ H-Dagg _ .f-el h2)

record [Obj] : [Any] where
  constructor ‼
  open :[Obj]

  -- data:
  field Ob     : [Any]
  field H-Hom  : :H-Hom Ob
  field V-Hom  : :V-Hom Ob
  field H-Dagg : :H-Dagg Ob H-Hom
  field H|V    : :H|V Ob H-Hom V-Hom
  field H-Dagg|V : :H-Dagg|V Ob H-Hom V-Hom H-Dagg H|V

  -- helpers:
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

  private module V-Hom (2ob : _) = Set.[Ob] (V-Hom 2ob)
  open V-Hom public
    using ()
    renaming
    ( It   to V-Hom-It;
      El   to V-Hom-El;
      To   to V-Hom-To;
      is   to V-Hom-is;
      refl to V-Hom-refl;
      tran to V-Hom-tran )

  private module H|V = Matr.[PoSet|Set] H|V
  open H|V public
    using ( Sqr; H-lact; H-ract; V-lact; V-ract )

  -- vertical is tight, horizontal is loose
  H-Ob : DaggPoSet-Qu.[Obj]
  H-Ob = ‼ Ob H-Hom H-Dagg
  V-Ob : Set-Qu.[Obj]
  V-Ob = ‼ Ob V-Hom

open [Obj] public
  using (H-Ob; V-Ob)
