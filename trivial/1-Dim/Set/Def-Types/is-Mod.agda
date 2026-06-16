open import 0-Dim.!quali
import 1-Dim.Graph.Def-Types.Mod as Graph
open import 1-Dim.Graph.Def-Types-pub.Mod
open import 1-Dim.Set.Def-Types.Ob
open import 1-Dim.Set.Def-Types-pub.Ob

--
-- define (Mod)ules on (Set)oids
--
module 1-Dim.Set.Def-Types.is-Mod where

module _ (AB @(A ~ B) : [2~] [Ob]) where
  :Mod : [Any]
  :Mod = Graph.[Mod] (A .It ~ B .It)

  module :is-Mod (M : :Mod) where
    -- (left/right) actions on relations
    :lact = Any.Rel-[2Fun] _ ((A .To × M .M-ob) > M .M-ob)
    :ract = Any.Rel-[2Fun] _ ((M .M-ob × B .To) > M .M-ob)

  record [is-Mod] (M : :Mod) : [Any] where
    constructor ‼
    open :is-Mod M
    field lact : :lact
    field ract : :ract
