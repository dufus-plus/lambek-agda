open import 0-Dim
import 1-Dim.Graph.Defs.Fun as Graph
open import 1-Dim.Set.Defs.Ob

--
-- define (Fun)ctions on (Set)oids
--
module 1-Dim.Set.Defs.Fun where

module _ (AB @(A > B) : [2~] [Ob]) where
  open [Ob]
  :Fun = Graph.[Fun] (A .↓ > B .↓)

record [Fun] (AB : [2~] [Ob]) : [Any] where
  constructor ‼
  field ↓ : :Fun AB
  open Graph.[Fun] ↓ public
