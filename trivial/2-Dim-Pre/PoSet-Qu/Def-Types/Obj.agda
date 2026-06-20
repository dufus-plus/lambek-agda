open import 0-Dim.!quali
import 2-Dim-Pre.Matr.Def-Types as AnyPoSet
import 1-Dim.PoSet.Def-Types as PoSet

module 2-Dim-Pre.PoSet-Qu.Def-Types.Obj where

--
-- Graph-enriched 2-Graph aka Globular PoSet-Quiver
--
module _ (Ob : [Any]) where
  -- type of 1-cells
  [is-Obj] = Matr.[PoSet] (2~ Ob)

record [Obj] : [Any] where
  constructor ‼

  -- cell types:
  field Ob  : [Any]
  field Hom : [is-Obj] Ob

  -- helper:
  private module Hom (2ob : [2~] Ob) = PoSet.[Ob] (Hom 2ob)
  open Hom public
    using ()
    renaming
    ( It   to Hom-It;
      El   to Hom-El;
      To   to Hom-To;
      is   to Hom-is;
      refl to Hom-refl;
      tran to Hom-tran )
