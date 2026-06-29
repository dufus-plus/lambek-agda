open import 0-Dim.!quali
import 1-Dim.Set.Def-Types as Set
import 1-Dim.PoSet.Def-Types as PoSet
import 1-Dim.Graph.Def-Types as Graph
open import 1-Dim.Set.Def-Types-pub
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.Graph.Def-Types-pub

module 1-Dim.PoSet.Conv.Objs where

Free : Graph.[Ob] → PoSet.[Ob]
Free G .It .El = G .El
Free G .It .To = [nPath] (G .El) (G .To)
Free G .is .refl el = nPath.Id _ _ el
Free G .is .tran _ 2npath = nPath.Mu _ _ _ 2npath

From-Set : Set.[Ob] → PoSet.[Ob]
From-Set S .It = S .It
From-Set S .is .refl = S .refl
From-Set S .is .tran = S .tran
