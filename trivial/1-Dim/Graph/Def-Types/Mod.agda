open import 0-Dim.!quali
open import 1-Dim.Graph.Def-Types.Ob

--
-- define (Mod)ules on (Gra)phs
--
module 1-Dim.Graph.Def-Types.Mod where

module _ (AB @(A ~ B) : [2~] [Ob]) where
  module :[Mod] where
    open [Ob]

    -- relation on elements
    :M-ob = Any.[Rel] (A .Ob ~ B .Ob)

  record [Mod] : [Any] where
    constructor ↑
    open :[Mod]
    field M-ob : :M-ob
