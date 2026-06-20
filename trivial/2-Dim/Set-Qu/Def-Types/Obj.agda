open import 0-Dim.!quali
import 1-Dim.AnySet.Def-Types as AnySet
import 1-Dim.Set.Def-Types as Set

module 2-Dim.Set-Qu.Def-Types.Obj where

-- Set-enriched 2-Graph aka Globular Set-Quiver
module _ (Ob : [Any]) where
  -- type of 1-cells
  [is-Obj] = AnySet.[Rel] (2~ Ob)

record [Obj] : [Any] where
  constructor ‼

  -- cell types:
  field Ob  : [Any]
  field Hom : [is-Obj] Ob

  -- helper:
  private module Hom (2ob : [2~] Ob) = Set.[Ob] (Hom 2ob)
  open Hom public
    using ()
    renaming
    ( It to Hom-It;
      El to Hom-El;
      To to Hom-To;
      is to Hom-is;
      refl to Hom-refl;
      tran to Hom-tran )
