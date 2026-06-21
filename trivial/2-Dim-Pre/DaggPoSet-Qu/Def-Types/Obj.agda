open import 0-Dim.!quali
import 2-Dim-Pre.Matr.Def-Types as Matr
import 1-Dim.PoSet.Def-Types as PoSet
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.Graph.Def-Types-pub

module 2-Dim-Pre.DaggPoSet-Qu.Def-Types.Obj where

--
-- Graph-enriched 2-Graph aka Globular PoSet-Quiver
--
module _ (Ob : [Any]) where
  -- type of 1-cells
  :Hom = Matr.[PoSet] (2~ Ob)
  module _ (Hom : :Hom) where
    :Dagg = Matr.PoSet-[S-Fun] _ (2~ Hom)

record [Obj] : [Any] where
  constructor ‼

  -- cell types:
  field Ob   : [Any]
  field Hom  : :Hom Ob
  field Dagg : :Dagg Ob Hom

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

  private module Dagg (2ob : [2~] Ob) = PoSet.[Fun] (Dagg 2ob)
  open Dagg public
    using ()
    renaming
    ( f-el to Dagg-el;
      f-to to Dagg-to )

module _ (O : [Any]) where
  Hom-Opp-Hom : :Hom O → :Hom O
  Hom-Opp-Hom Hom = Matr.PoSet-Hom-Opp _ Hom

  To-Opp-Hom : :Hom O → :Hom O
  To-Opp-Hom Hom = Matr.PoSet-To-Opp _ Hom

module _ where
  open [Obj]

  Hom-Opp : [Obj] → [Obj]
  Hom-Opp Qu .Ob  = Qu .Ob
  Hom-Opp Qu .Hom = Hom-Opp-Hom _ (Qu .Hom)
  Hom-Opp Qu .Dagg _ .↓ .f-el h     = Qu .Dagg _ .f-el h
  Hom-Opp Qu .Dagg _ .↓ .f-to _ hto = Qu .Dagg _ .f-to _ hto

  To-Opp : [Obj] → [Obj]
  To-Opp Qu .Ob  = Qu .Ob
  To-Opp Qu .Hom = To-Opp-Hom _ (Qu .Hom)
  To-Opp Qu .Dagg _ .↓ .f-el h     = Qu .Dagg _ .f-el h
  To-Opp Qu .Dagg _ .↓ .f-to _ hto = Qu .Dagg _ .f-to _ hto
