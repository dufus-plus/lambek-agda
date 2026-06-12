open import 0-Dim
import 1-Dim.Graph.Defs.Fun-To as Graph
open import 1-Dim.Set.Defs.Ob
open import 1-Dim.Set.Defs.Fun

module 1-Dim.Set.Defs.Fun-To where

-- relation on functions
module _ (AB @(A > B) : [2~] [Ob]) (2f @(f1 ~ f2) : [2~] [Fun] (A > B)) where
  open [Fun]
  :Fun-To = Graph.:Fun-To _ (f1 .↓ > f2 .↓)

record Fun-[To] (AB : [2~] [Ob]) (2f : [2~] [Fun] AB) : [Any] where
  constructor ↑
  field ↓ : :Fun-To AB 2f
