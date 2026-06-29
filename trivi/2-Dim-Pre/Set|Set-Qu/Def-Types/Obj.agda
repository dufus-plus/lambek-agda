open import 0-Dim.!quali
import 1-Dim.Set.Def-Types.Ob as Set
import 2-Dim-Pre.Matr.Def-Types as Matr
import 2-Dim-Pre.Set-Qu.Def-Types.Obj as Set-Qu

module 2-Dim-Pre.Set|Set-Qu.Def-Types.Obj where

open Set-Qu using (‼)

--
-- Double Quiver aka Cubical 2-Graph:
-- the Carrier for Double 1-Categories
--
module :[Obj] where
  open Set.[Ob]
  module _ (Ob : Any) where
    -- type of 1-cells
    :H-Hom = Matr.[Set] (2~ Ob)
    :V-Hom = Matr.[Set] (2~ Ob)
    module _ (H-Hom : :H-Hom) (V-Hom : :V-Hom) where
      -- type of 2-cells as 2-module
      :H|V = Matr.[Set|Set] _ (2~ V-Hom) (2~ H-Hom)

record [Obj] : Any where
  constructor ‼
  open :[Obj]

  -- data:
  field Ob : Any
  field H-Hom : :H-Hom Ob
  field V-Hom : :V-Hom Ob
  field H|V : :H|V Ob H-Hom V-Hom

  -- helpers:
  private module H-Hom (2ob : _) = Set.[Ob] (H-Hom 2ob)
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

  private module H|V = Matr.[Set|Set] H|V
  open H|V public
    using ( Sqr; H-lact; H-ract; V-lact; V-ract )

  -- vertical is tight, horizontal is loose
  H-Ob : Set-Qu.[Obj]
  H-Ob = ‼ Ob H-Hom
  V-Ob : Set-Qu.[Obj]
  V-Ob = ‼ Ob V-Hom

open [Obj] public
  using (H-Ob; V-Ob)
