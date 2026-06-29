open import 0-Dim.!quali
import 2-Dim-Pre.Matr.Def-Types as Matr
import 1-Dim.Graph.Def-Types as Graph

module 2-Dim-Pre.Graph-Qu.Def-Types.Obj where

-- Graph-enriched Graph aka Globular Quiver
module :[Obj] where
  -- type of 0-cells
  module _ (Ob : Any) where
    -- type of 1-cells
    :Hom = Matr.[Graph] (2~ Ob)

record [Obj] : Any where
  constructor ‼
  open :[Obj]

  -- cell types:
  field Ob  : Any
  field Hom : :Hom Ob

  -- helper:
  private module Hom (2ob : [2~] Ob) = Graph.[Ob] (Hom 2ob)
  open Hom using () renaming
    ( El to Hom-El;
      To to Hom-To ) public
