open import 0-Dim.!quali
import 1-Dim.Graph.Def-Types.Ob as Graph
import 1-Dim.PoSet.Def-Types.Ob as PoSet
import 1-Dim.Set.Def-Types.Ob as Set
open import 1-Dim.Graph.Def-Types-pub.Ob

module 1-Dim.Graph.Conv.Objs where

From-PoSet : PoSet.[Ob] → Graph.[Ob]
From-PoSet = PoSet.[Ob].It

From-Set : Set.[Ob] → Graph.[Ob]
From-Set = Set.[Ob].It

Symm-Or : Graph.[Ob] → Graph.[Ob]
Symm-Or G .El = G .El
Symm-Or G .To (a ~ b) = G .To (a ~ b) [+] G .To (b ~ a)

Symm-And : Graph.[Ob] → Graph.[Ob]
Symm-And G .El = G .El
Symm-And G .To (a ~ b) = [⊣] (G .To) (a ~ b)
