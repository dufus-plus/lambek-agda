open import 0-Dim-qua
open import 1-Dim.Graph-pub
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Def-Gens.Objs

module 1-Dim.PoSet.Def-Gens.Unit where

module Unit where
  module _ (A : [Ob]) where
    Term : [Fun] (A > Unit)
    Term .↓ = Graph.Unit.Term (A .It)

  ob = Unit
