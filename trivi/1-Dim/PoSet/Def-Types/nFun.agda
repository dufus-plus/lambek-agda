open import 0-Dim.!quali
open import 1-Dim.PoSet.Def-Types.Ob
open import 1-Dim.PoSet.Def-Types-pub.Ob
open import 1-Dim.PoSet.Def-Types.Fun
open import 1-Dim.PoSet.Def-Gens.Objs

module 1-Dim.PoSet.Def-Types.nFun where

[0-Fun] : [!] [~] [Ob] → Any
[0-Fun] (_ > A) = A .El

[2-Fun] : ([2×] [Ob]) [~] [Ob] → Any
[2-Fun] (2A > B) = [Fun] (Prod2 2A > B)
