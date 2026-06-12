open import 0-Dim
open import 1-Dim.Graph-pub
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Gens.Objs

module 1-Dim.PoSet.Gens.Void where

module Void where
  module _ (A : [Ob]) where
    Init : [Fun] (Void > A)
    Init .↓ = Graph.Void.Init (A .↓)

  ob = Void
