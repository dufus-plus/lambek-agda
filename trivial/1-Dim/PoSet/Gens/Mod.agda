open import 0-Dim
open import 1-Dim.Graph-pub
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
import 1-Dim.AnyPoSet.Defs as AnyPoSet

module 1-Dim.PoSet.Gens.Mod where

module _ (AB @ (A > B) : [2~] [Ob]) where
  Mod : [Ob] -- PoSet
  Mod .↓ .Ob = [Mod] (A ~ B)
  Mod .↓ .To = Mod-[Fun] _
  Mod .is .refl M .↓ _ = ⑴
  Mod .is .tran _ (rto12 × rto23) .↓ _ = rto12 .↓ _ ∘ rto23 .↓ _
