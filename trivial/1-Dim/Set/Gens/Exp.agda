open import 0-Dim
import 1-Dim.Graph.Defs.Ob as Graph
open import 1-Dim.Set.Defs.Ob
open import 1-Dim.Set.Defs.Fun
open import 1-Dim.Set.Defs.Fun-To

module 1-Dim.Set.Gens.Exp where

open [Ob]
open [is]
open [Fun]
open Fun-[To]
open Graph.[Ob]

module _ (AB @ (A > B) : [2~] [Ob]) where
  Fun:S : [Ob] -- Set
  Fun:S .↓ .Ob = [Fun] (A > B)
  Fun:S .↓ .To = Fun-[To] _
  Fun:S .is .refl f .↓ a = B .refl (f .f-ob a)
  Fun:S .is .symm (f1 ~ f2) (- fto21) .↓ a = B .symm _ (- fto21 .↓ a)
  Fun:S .is .tran (f1 ~ f2 ~ f3) (fto12 × fto23) .↓ a =
    B .tran _ (fto12 .↓ a × fto23 .↓ a)

Exp = Fun
