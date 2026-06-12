open import 0-Dim
open import 1-Dim.PoSet.Def-Types.Ob
open import 1-Dim.PoSet.Def-Types.Fun
open import 1-Dim.PoSet.Gens.Objs

module 1-Dim.PoSet.Def-Types.nFun where

open [Ob]

[0Fun] : [!] [~] [Ob] → [Any]
[0Fun] (_ > A) = [Fun] (Unit > A)

[2Fun] : ([2×] [Ob]) [~] [Ob] → [Any]
[2Fun] (2A > B) = [Fun] (Prod2 2A > B)
