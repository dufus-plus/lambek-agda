open import 0-Dim
open import 1-Dim.Graph-pub
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub

module 1-Dim.PoSet.Gens.Fun where

module _ (AB @ (A > B) : [2~] [Ob]) where
  Fun : [Ob] -- Poset
  Fun .↓ .Ob = [Fun] (A > B)
  Fun .↓ .To (f ~ g) = Fun-[To] _ (f ~ g)
  Fun .is .refl f .↓ a = B .refl (f .f-ob a)
  Fun .is .tran (f1 ~ f2 ~ f3) (fto12 × fto23) .↓ a =
    B .tran _ (fto12 .↓ a × fto23 .↓ a)

Exp = Fun
