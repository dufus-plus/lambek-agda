open import 0-Dim
import 1-Dim.Graph.Defs.Fun as Graph
open import 1-Dim.Set.Defs.Ob
open import 1-Dim.Set.Defs.Fun
open import 1-Dim.Set.Defs.Fun-To
open import 1-Dim.Set.Gens.Exp
import 1-Dim.AnySet.Defs as AnySet

module 1-Dim.Set.Oper.Fun where

open [Ob]
open [Fun]
open Fun-[To]
open Graph.[Fun]

Fun-Id : AnySet.Rel-[0Fun] _ (! > Fun)
Fun-Id _ .↓ .f-ob = ⑴
Fun-Id _ .↓ .f-to _ = ⑴

Fun-Mu : AnySet.Rel-[2Fun] _ ((Fun × Fun) > Fun)
Fun-Mu _ .↓ .f-ob (fab × fbc) .↓ .f-ob   = fab .f-ob   ∘ fbc .f-ob
Fun-Mu _ .↓ .f-ob (fab × fbc) .↓ .f-to _ = fab .f-to _ ∘ fbc .f-to _
Fun-Mu (A ~ B ~ C) .↓ .f-to ((fab × fbc) ~ (gab × gbc)) (to12 × to23) .↓ a =
  C .tran _ ((fbc .f-to _ (to12 .↓ a)) × (to23 .↓ (gab .f-ob a)))
