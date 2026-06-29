open import 0-Dim.!quali
import 1-Dim.Graph.Def-Types.Mod as Graph
open import 1-Dim.Graph.Def-Types-pub.Mod
open import 1-Dim.PoSet.Def-Types.Ob
open import 1-Dim.PoSet.Def-Types-pub.Ob

--
-- define (Mod)ules on Po(Set)oids
--
module 1-Dim.PoSet.Def-Types.is-Mod where

module _ (AB @(A ~ B) : [2~] [Ob]) where
  :Mod = Graph.[Mod] (A .It ~ B .It)

  module :[is-Mod] (M : :Mod) where
    -- (left/right) actions on relations
    :lact = Any.Rel-[2-Fun] _ ((A .To × M .M-ob) > M .M-ob)
    :ract = Any.Rel-[2-Fun] _ ((M .M-ob × B .To) > M .M-ob)

  record [is-Mod] (Mod : :Mod) : Any where
    constructor ‼
    open :[is-Mod]
    field lact : :lact Mod
    field ract : :ract Mod
