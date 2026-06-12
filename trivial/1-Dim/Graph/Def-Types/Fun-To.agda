open import 0-Dim
open import 1-Dim.Graph.Def-Types.Ob
open import 1-Dim.Graph.Def-Types.Fun

module 1-Dim.Graph.Def-Types.Fun-To where

-- relation on functions
module _ (AB @(A > B) : [2~] [Ob]) (2f @(f1 ~ f2) : [2~] [Fun] (A > B)) where
  open [Ob]
  open [Fun]

  :Fun-To : [Any]
  :Fun-To = Any.[Rel|0Fun] _ (f1 .f-ob ~ f2 .f-ob) (! > B .To)

  record Fun-[To] : [Any] where
    constructor ↑
    field ↓ : :Fun-To
