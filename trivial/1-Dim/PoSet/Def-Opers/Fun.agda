open import 0-Dim
open import 1-Dim.Graph
open import 1-Dim.PoSet.Def-Types.Ob
open import 1-Dim.PoSet.Def-Types.Fun
open import 1-Dim.PoSet.Def-Types.Fun-To
open import 1-Dim.PoSet.Def-Types-pub.Ob
open import 1-Dim.PoSet.Def-Types-pub.Fun
open import 1-Dim.PoSet.Def-Types-pub.Fun-To
open import 1-Dim.PoSet.Gens.Fun
import 1-Dim.AnyPoSet.Defs as AnyPoSet

module 1-Dim.PoSet.Def-Opers.Fun where

open Graph.[Fun]

Fun-Id : AnyPoSet.Rel-[0Fun] _ (! > Fun)
Fun-Id _ .↓ .f-ob = ⑴
Fun-Id _ .↓ .f-to _ = ⑴

Fun-Mu : AnyPoSet.Rel-[2Fun] _ ((Fun × Fun) > Fun)
Fun-Mu _ .↓ .f-ob (fab × fbc) .↓ .f-ob   = fab .f-ob   ∘ fbc .f-ob
Fun-Mu _ .↓ .f-ob (fab × fbc) .↓ .f-to _ = fab .f-to _ ∘ fbc .f-to _
Fun-Mu (A ~ B ~ C) .↓ .f-to ((fab × fbc) ~ (gab × gbc)) (toab × tobc) .↓ a =
  C .tran _ ((fbc .f-to _ (toab .↓ a)) × (tobc .↓ (gab .f-ob a)))
