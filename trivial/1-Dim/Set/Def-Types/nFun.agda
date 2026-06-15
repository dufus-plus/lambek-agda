open import 0-Dim-qua
open import 1-Dim.Set.Def-Types.Ob
open import 1-Dim.Set.Def-Types-pub.Ob
open import 1-Dim.Set.Def-Types.Fun
open import 1-Dim.Set.Def-Gens.Objs

module 1-Dim.Set.Def-Types.nFun where

[0Fun] : [!] [~] [Ob] → [Any]
[0Fun] (_ > A) = A .Ob

[2Fun] : ([2×] [Ob]) [~] [Ob] → [Any]
[2Fun] (2A > B) = [Fun] (Prod2 2A > B)
