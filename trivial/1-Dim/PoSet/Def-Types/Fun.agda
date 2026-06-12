open import 0-Dim
import 1-Dim.Graph.Def-Types.Fun as Graph
open import 1-Dim.PoSet.Def-Types.Ob

--
-- define (Fun)ctions on Po(Set)oids
--
module 1-Dim.PoSet.Def-Types.Fun where

module _ (AB @(A > B) : [2~] [Ob]) where
  open [Ob]
  :Fun = Graph.[Fun] (A .↓ > B .↓)

record [Fun] (AB : [2~] [Ob]) : [Any] where
  constructor ‼
  field ↓ : :Fun AB
  open Graph.[Fun] ↓ public
