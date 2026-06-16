open import 0-Dim.!quali
open import 1-Dim.Graph.Def-Types
open import 1-Dim.Graph.Def-Types-pub
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet
import 1-Dim.PoSet.Def-Types as PoSet
open import 1-Dim.PoSet.Def-Types-pub

module 1-Dim.Graph.Def-Opers.Fun where

-- module _ (AB : [2~] [Ob]) where
--   Fun : PoSet.[Ob]
--   Fun .It .Ob = [Fun] AB
--   Fun .It .To = Fun-[Id] _
--   Fun .is .refl _ .↓ _ = ≡ _
--   Fun .is .tran _ (to12 × to23) .↓ _ = ≡.tran (to12 .↓ _ × to23 .↓ _)

Fun-Id : Any.Rel-[0Fun] _ (! > [Fun])
Fun-Id _ .f-ob = ⑴
Fun-Id _ .f-to _ = ⑴

Fun-Mu : Any.Rel-[2Fun] _ (([Fun] × [Fun]) > [Fun])
Fun-Mu _ (fab × fbc) .f-ob   = fab .f-ob   ∘ fbc .f-ob
Fun-Mu _ (fab × fbc) .f-to _ = fab .f-to _ ∘ fbc .f-to _
