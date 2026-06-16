open import 0-Dim.!quali
import 1-Dim.Graph.Def-Types as Graph
open import 1-Dim.Graph.Def-Types-pub
open import 1-Dim.Set.Def-Types
open import 1-Dim.Set.Def-Types-pub
import 1-Dim.AnySet.Def-Types as AnySet
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet
import 1-Dim.PoSet.Def-Types as PoSet
open import 1-Dim.PoSet.Def-Types-pub

module 1-Dim.Set.Def-Opers.Fun where

module _ (AB @ (A > B) : [2~] [Ob]) where
  Fun : [Ob] -- Set
  Fun .It .Ob = [Fun] (A > B)
  Fun .It .To = Fun-[To] _
  Fun .is .refl f .↓ a = B .refl (f .f-ob a)
  Fun .is .symm (f1 ~ f2) (- fto21) .↓ a = B .symm _ (- fto21 .↓ a)
  Fun .is .tran (f1 ~ f2 ~ f3) (fto12 × fto23) .↓ a =
    B .tran _ (fto12 .↓ a × fto23 .↓ a)

Fun-Id : AnySet.Rel-[0Fun] _ (! > Fun)
Fun-Id _ .↓ .f-ob = ⑴
Fun-Id _ .↓ .f-to _ = ⑴

Fun-Mu : AnySet.Rel-[2Fun] _ ((Fun × Fun) > Fun)
Fun-Mu _ .↓ .f-ob (fab × fbc) .↓ .f-ob   = fab .f-ob   ∘ fbc .f-ob
Fun-Mu _ .↓ .f-ob (fab × fbc) .↓ .f-to _ = fab .f-to _ ∘ fbc .f-to _
Fun-Mu (A ~ B ~ C) .↓ .f-to ((fab × fbc) ~ (gab × gbc)) (to12 × to23) .↓ a =
  C .tran _ ((fbc .f-to _ (to12 .↓ a)) × (to23 .↓ (gab .f-ob a)))

-- TODO conversion func
module _ (AB @ (A > B) : [2~] [Ob]) where
  Fun:PS : PoSet.[Ob] -- Set
  Fun:PS .It .Ob = [Fun] (A > B)
  Fun:PS .It .To = Fun-[To] _
  Fun:PS .is .refl f .↓ a = B .refl (f .f-ob a)
  Fun:PS .is .tran (f1 ~ f2 ~ f3) (fto12 × fto23) .↓ a =
    B .tran _ (fto12 .↓ a × fto23 .↓ a)

Fun:PS-Id : AnyPoSet.Rel-[0Fun] _ (! > Fun:PS)
Fun:PS-Id _ .↓ .f-ob = ⑴
Fun:PS-Id _ .↓ .f-to _ = ⑴

Fun:PS-Mu : AnyPoSet.Rel-[2Fun] _ ((Fun:PS × Fun:PS) > Fun:PS)
Fun:PS-Mu _ .↓ .f-ob (fab × fbc) .↓ .f-ob   = fab .f-ob   ∘ fbc .f-ob
Fun:PS-Mu _ .↓ .f-ob (fab × fbc) .↓ .f-to _ = fab .f-to _ ∘ fbc .f-to _
Fun:PS-Mu (A ~ B ~ C) .↓ .f-to ((fab × fbc) ~ (gab × gbc)) (to12 × to23) .↓ a =
  C .tran _ ((fbc .f-to _ (to12 .↓ a)) × (to23 .↓ (gab .f-ob a)))
