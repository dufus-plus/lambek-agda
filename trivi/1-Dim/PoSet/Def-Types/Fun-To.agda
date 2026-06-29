open import 0-Dim.!quali
import 1-Dim.Graph.Def-Types.Fun-To as Graph
open import 1-Dim.PoSet.Def-Types.Fun
open import 1-Dim.PoSet.Def-Types-pub.Fun

module 1-Dim.PoSet.Def-Types.Fun-To where

-- relation on functions
module _ (AB : [2~] _) (2f @(f1 ~ f2) : [2~] [Fun] AB) where

  :Fun-To : Any
  :Fun-To = Graph.:Fun-To _ (f1 .↓ > f2 .↓)

  record Fun-[To] : Any where
    constructor ↑
    field ↓ : :Fun-To
