open import 0-Dim.!quali
import 2-Dim-Pre.Matr.Def-Types as Matr
import 1-Dim.Set.Def-Types as Set

module 2-Dim-Pre.Set-Qu.Def-Types.Obj where

-- Set-enriched 2-Graph aka Globular Set-Quiver
module _ (Ob : Any) where
  -- type of 1-cells
  :Hom = Matr.[Set] (2~ Ob)

record [Obj] : Any where
  constructor ‼

  -- cell types:
  field Ob  : Any
  field Hom : :Hom Ob

  -- helper:
  private module Hom (2ob : [2~] Ob) = Set.[Ob] (Hom 2ob)
  open Hom public
    using ()
    renaming
    ( It   to Hom-It;
      El   to Hom-El;
      To   to Hom-To;
      is   to Hom-is;
      refl to Hom-refl;
      symm to Hom-symm;
      tran to Hom-tran )

module _ (O : Any) where
  Hom-Opp-Hom : :Hom O → :Hom O
  Hom-Opp-Hom Hom = Matr.Set-Hom-Opp _ Hom

  To-Opp-Hom : :Hom O → :Hom O
  To-Opp-Hom Hom = Matr.Set-To-Opp _ Hom

module _ where
  open [Obj]

  Hom-Opp : [Obj] → [Obj]
  Hom-Opp Qu .Ob  = Qu .Ob
  Hom-Opp Qu .Hom = Hom-Opp-Hom _ (Qu .Hom)

  To-Opp : [Obj] → [Obj]
  To-Opp Qu .Ob  = Qu .Ob
  To-Opp Qu .Hom = To-Opp-Hom _ (Qu .Hom)
