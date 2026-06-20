open import 0-Dim.!quali
import 2-Dim-Pre.AnyGraph.Def-Types as AnyGraph
import 1-Dim.Graph.Def-Types as Graph
open import 2-Dim-Pre.Graph-Qu.Def-Types.Obj
open import 2-Dim-Pre.Graph-Qu.Def-Types-pub.Obj

--
-- define (Fun)ctions on (Gra)phs
--
module 2-Dim-Pre.Graph-Qu.Def-Types.Fun where

module _ (AB @(A > B) : [2~] [Obj]) where
  module :[Fun] where
    -- function on 0-cells
    :f-ob = AnyGraph.[Fun] (A .Ob > B .Ob)
    module _ (f-ob : :f-ob) where
      -- function on 1-cells
      :f-hom = AnyGraph.[Rel|Fun] _ (f-ob ~ f-ob) (A .Hom ~ B .Hom)

  record [Fun] : [Any] where
    constructor ‼
    open :[Fun]

    -- (f)unctions between Graph cells:
    field f-ob : :f-ob
    field f-hom : :f-hom f-ob

    -- helper:
    private module f-hom (2ob : _) = Graph.[Fun] (f-hom 2ob)
    open f-hom using () renaming
      ( f-el to f-hom-el;
        f-to to f-hom-to ) public
