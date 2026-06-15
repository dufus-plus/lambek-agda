open import 0-Dim-qua
open import 1-Dim.Graph.Def-Types.Ob

--
-- define (Fun)ctions on (Gra)phs
--
module 1-Dim.Graph.Def-Types.Fun where

module _ (AB @(A > B) : [2~] [Ob]) where
  module :[Fun] where
    open [Ob]
    -- function on elements
    :f-ob = Any.[Fun] (A .Ob > B .Ob)
    module _ (f-ob : :f-ob) where
      -- function on relations
      :f-to = Any.[Rel|Fun] _ (f-ob ~ f-ob) (A .To ~ B .To)

  record [Fun] : [Any] where
    constructor ‼
    open :[Fun]
    field f-ob : :f-ob
    field f-to : :f-to f-ob
