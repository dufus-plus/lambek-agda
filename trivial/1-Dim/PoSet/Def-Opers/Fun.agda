open import 0-Dim.!quali
import 1-Dim.Graph.Def-Types as Graph
open import 1-Dim.Graph.Def-Types-pub
open import 1-Dim.PoSet.Def-Types.Ob
open import 1-Dim.PoSet.Def-Types.Fun
open import 1-Dim.PoSet.Def-Types.Fun-To
open import 1-Dim.PoSet.Def-Types-pub.Ob
open import 1-Dim.PoSet.Def-Types-pub.Fun
open import 1-Dim.PoSet.Def-Types-pub.Fun-To
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet

module 1-Dim.PoSet.Def-Opers.Fun where

module _ (AB @ (A > B) : [2~] [Ob]) where
  Fun : [Ob] -- Poset
  Fun .It .El = [Fun] (A > B)
  Fun .It .To (f ~ g) = Fun-[To] _ (f ~ g)
  Fun .is .refl f .↓ a = B .refl (f .f-el a)
  Fun .is .tran (f1 ~ f2 ~ f3) (fto12 × fto23) .↓ a =
    B .tran _ (fto12 .↓ a × fto23 .↓ a)

Fun-Id : AnyPoSet.Rel-[0-Fun] _ (! > Fun)
Fun-Id _ .↓ .f-el = ⑴
Fun-Id _ .↓ .f-to _ = ⑴

Fun-Mu : AnyPoSet.Rel-[2-Fun] _ ((Fun × Fun) > Fun)
Fun-Mu _ .↓ .f-el (fab × fbc) .↓ .f-el   = fab .f-el   ∘ fbc .f-el
Fun-Mu _ .↓ .f-el (fab × fbc) .↓ .f-to _ = fab .f-to _ ∘ fbc .f-to _
Fun-Mu (A ~ B ~ C) .↓ .f-to ((fab × fbc) ~ (gab × gbc)) (toab × tobc) .↓ a =
  C .tran _ ((fbc .f-to _ (toab .↓ a)) × (tobc .↓ (gab .f-el a)))
