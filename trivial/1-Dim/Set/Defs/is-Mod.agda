open import 0-Dim
import 1-Dim.Graph.Defs.Mod as Graph
open import 1-Dim.Set.Defs.Ob

--
-- define (Mod)ules on (Set)oids
--
module 1-Dim.Set.Defs.is-Mod where

module _ (AB @(A ~ B) : [2~] [Ob]) where
  open [Ob]
  :Mod = Graph.[Mod] (A .↓ ~ B .↓)
  module :is-Mod (M : :Mod) where
    open Graph.[Mod]
    -- (left/right) actions on relations
    :lact = Any.Rel-[2Fun] _ ((A .To × M .M-ob) > M .M-ob)
    :ract = Any.Rel-[2Fun] _ ((M .M-ob × B .To) > M .M-ob)

  record [is-Mod] (M : :Mod) : [Any] where
    constructor ‼
    open :is-Mod M
    field lact : :lact
    field ract : :ract
