open import 0-Dim-qua
import 1-Dim.Graph.Def-Types.Fun as Graph
open import 1-Dim.Set.Def-Types.Ob
open import 1-Dim.Set.Def-Types-pub.Ob

--
-- define (Fun)ctions on (Set)oids
--
module 1-Dim.Set.Def-Types.Fun where

module _ (AB @(A > B) : [2~] [Ob]) where
  :Fun : [Any]
  :Fun = Graph.[Fun] (A .It > B .It)

  record [Fun] : [Any] where
    constructor ‼
    field ↓ : :Fun
    open Graph.[Fun] ↓ public
