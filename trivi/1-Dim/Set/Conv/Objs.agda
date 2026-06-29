open import 0-Dim.!quali
open import 1-Dim.Graph.!publi
import 1-Dim.Set.Def-Types as Set
open import 1-Dim.Set.Def-Types-pub

module 1-Dim.Set.Conv.Objs where

From-Graph-And : Graph.[Ob] → Set.[Ob]
From-Graph-And G .It .El = G .El
From-Graph-And G .It .To = [nPath] (G .El) (Graph.Symm-And G .To)
From-Graph-And G .is .refl el = nPath.Id _ _ el
From-Graph-And G .is .tran _ 2np = nPath.Mu _ _ _ 2np
From-Graph-And G .is .symm _ np =
  nPath.Map _ _ (⊣.symm (G .To)) _ (nPath.Rev _ _ _ np)

From-Graph-Or : Graph.[Ob] → Set.[Ob]
From-Graph-Or G .It .El = G .El
From-Graph-Or G .It .To = [nPath] (G .El) (Graph.Symm-Or G .To)
From-Graph-Or G .is .refl el = nPath.Id _ _ el
From-Graph-Or G .is .tran _ 2np = nPath.Mu _ _ _ 2np
From-Graph-Or G .is .symm _ np =
  nPath.Map _ _ (λ _ → +.symm) _ (nPath.Rev _ _ _ np)
