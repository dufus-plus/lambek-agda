open import 0-Dim
open import 1-Dim.Graph.Def-Types.Ob
open import 1-Dim.Graph.Def-Types.Fun
open import 1-Dim.Graph.Def-Types.Fun-To
open import 1-Dim.Graph.Def-Types-pub.Ob

module 1-Dim.Graph.Gens.Exp where

open [Ob]

module _ (AB : [2~] [Ob]) where
  Fun : [Ob] -- Graph
  Fun .Ob = [Fun] AB
  Fun .To = Fun-[To] _

Exp = Fun -- non-cartesian
