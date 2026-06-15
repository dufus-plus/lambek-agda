open import 0-Dim
open import 1-Dim.Graph-pub
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Gens.Objs

module 1-Dim.PoSet.Gens.Summ2 where

module Summ2 where
  module _ ((A + B) : [Ob] [×] [Ob]) where
    Inj1 : [Fun] (A > Summ2 (A + B))
    Inj1 .↓ = Graph.Summ2.Inj1 (A .↓ + B .↓)
    Inj2 : [Fun] (B > Summ2 (A + B))
    Inj2 .↓ = Graph.Summ2.Inj2 (A .↓ + B .↓)
  module _ (X : [Ob]) where
    Glue : [Fun] (Summ2 (X + X) > X)
    Glue .↓ = Graph.Summ2.Glue (X .↓)

  oper = Summ2
