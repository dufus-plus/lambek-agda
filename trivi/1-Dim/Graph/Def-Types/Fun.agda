open import 0-Dim.!quali
open import 1-Dim.Graph.Def-Types.Ob

--
-- define (Fun)ctions on (Gra)phs
--
module 1-Dim.Graph.Def-Types.Fun where

module _ (AB @(A > B) : [2~] [Ob]) where
  module :[Fun] where
    open [Ob]
    -- function on elements
    :f-el = Any.[Fun] (A .El > B .El)
    module _ (f-el : :f-el) where
      -- function on relations
      :f-to = Any.[Rel|Fun] _ (f-el ~ f-el) (A .To ~ B .To)

  record [Fun] : Any where
    constructor ‼
    open :[Fun]
    field f-el : :f-el
    field f-to : :f-to f-el
