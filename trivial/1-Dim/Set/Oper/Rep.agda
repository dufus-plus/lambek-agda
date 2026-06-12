open import 0-Dim
import 1-Dim.Graph.Defs.Mod as Graph
open import 1-Dim.Set.Defs.Ob
open import 1-Dim.Set.Defs.Fun
open import 1-Dim.Set.Defs.Mod
open import 1-Dim.Set.Defs.Fun-To
import 1-Dim.AnySet.Defs as AnySet

module 1-Dim.Set.Oper.Rep where

open [Ob]
open [Fun]
open [Mod]
open [is-Mod]
open Graph.[Mod]

-- representable and corepresentable modules
Rep+ : Any.Rel-[Fun] _ ([Fun] > [Mod])
Rep+ (A ~ B) f .↓ .M-ob (a ~ b) = B .To (f .f-ob a ~ b)
Rep+ (A ~ B) f .is .lact _ (ato12 × rab) = B .tran _ (f .f-to _ ato12 × rab)
Rep+ (A ~ B) f .is .ract _ (rab × bto12) = B .tran _ (rab × bto12)

Rep- : Any.Rel-[Fun] _ ([-] [Fun] > [Mod])
Rep- (B ~ A) (- f) .↓ .M-ob (b ~ a) = B .To (b ~ f .f-ob a)
Rep- (B ~ A) (- f) .is .lact _ (bto12 × rab) = B .tran _ (bto12 × rab)
Rep- (B ~ A) (- f) .is .ract _ (rab × ato12) = B .tran _ (rab × f .f-to _ ato12)

-- (Rest)riction
module _ (22A @((A11 ~ A12) ~ (A21 ~ A22)) : [22~] [Ob])
         (2f @(v1 ~ v2) : [Fun] (A11 > A21) [~] [Fun] (A12 > A22)) where
  Rel-Rest : [Mod] (A21 ~ A22) → [Mod] (A11 ~ A12)
  Rel-Rest h .↓ .M-ob (a11 ~ a12) = h .M-ob (v1 .f-ob a11 ~ v2 .f-ob a12)
  Rel-Rest h .is .lact _ (a11to × r) = h .lact _ (v1 .f-to _ a11to × r)
  Rel-Rest h .is .ract _ (r × a12to) = h .ract _ (r × v2 .f-to _ a12to)
