open import 0-Dim
open import 1-Dim.Graph.Def-Types.Ob
open import 1-Dim.Graph.Def-Types.Fun
open import 1-Dim.Graph.Def-Types.Fun-To
open import 1-Dim.Graph.Def-Types-pub.Ob
open import 1-Dim.Graph.Def-Types-pub.Fun
open import 1-Dim.Graph.Def-Types-pub.Fun-To
open import 1-Dim.Graph.Gens.Exp
import 1-Dim.AnyGraph.Defs as AnyGraph

module 1-Dim.Graph.Def-Opers.Fun where

Fun-Id : AnyGraph.Rel-[0Fun] _ (! > Fun)
Fun-Id _ .f-ob = ⑴
Fun-Id _ .f-to _ = ⑴

-- function composition on Graphs respects the *tensor* product on Graph
Fun-Mu : AnyGraph.Rel-[2Fun] _ ((Fun × Fun) > Fun)
Fun-Mu _ .f-ob (fab × fbc) .f-ob   = fab .f-ob   ∘ fbc .f-ob
Fun-Mu _ .f-ob (fab × fbc) .f-to _ = fab .f-to _ ∘ fbc .f-to _
Fun-Mu _ .f-to _ (↑₁ (fgto × (≡ fbc))) .↓ a = fbc .f-to _ (fgto .↓ a)
Fun-Mu _ .f-to _ (↑₂ ((≡ fab) × fgto)) .↓ a = fgto .↓ (fab .f-ob a)
