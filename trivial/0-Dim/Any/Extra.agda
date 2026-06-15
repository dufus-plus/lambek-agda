open import 0-Dim.Prelude
open import 0-Dim.Any.Def-Types
open import 0-Dim.Any.Def-Opers
open import 1-Dim.Graph.Def-Types-pub
import 1-Dim.PoSet.Def-Types.Ob as PoSet
open import 1-Dim.PoSet.Def-Types-pub.Ob

module 0-Dim.Any.Extra where

-- poset of propositions
Any:PS : PoSet.[Ob]
Any:PS .It .Ob = [Ob]
Any:PS .It .To = [Fun]
Any:PS .is .refl = Fun-Id
Any:PS .is .tran = Fun-Mu
