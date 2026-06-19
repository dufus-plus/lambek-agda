open import 0-Dim.!quali
import 1-Dim.AnyGraph.Def-Types as AnyGraph
import 1-Dim.Graph.Def-Types as Graph

module 2-Dim.Graph-Quiver.Def-Types.Obj where

-- Graph-enriched Graph aka Globular Quiver
module :[Obj] where
  -- type of 0-cells
  :Ob = AnyGraph.[Ob]
  module _ (Ob : :Ob) where
    -- type of 1-cells
    :Hom = AnyGraph.[Rel] (2~ Ob)

record [Obj] : [Any] where
  constructor ‼
  open :[Obj]

  -- cell types:
  field Ob  : :Ob
  field Hom : :Hom Ob

  -- helper:
  private module Hom (2ob : [2~] Ob) = Graph.[Ob] (Hom 2ob)
  open Hom using () renaming
    ( El to Hom-El;
      To to Hom-To ) public
