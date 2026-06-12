open import 0-Dim
open import 1-Dim.Graph
open import 1-Dim.PoSet.Def-Types.Ob
open import 1-Dim.PoSet.Def-Types.Fun
open import 1-Dim.PoSet.Def-Types.Mod
open import 1-Dim.PoSet.Def-Types.Fun-To
open import 1-Dim.PoSet.Def-Types.Mod|Fun
open import 1-Dim.PoSet.Def-Types-pub.Ob
open import 1-Dim.PoSet.Def-Types-pub.Fun
open import 1-Dim.PoSet.Def-Types-pub.Mod
open import 1-Dim.PoSet.Def-Types-pub.Fun-To
open import 1-Dim.PoSet.Def-Types-pub.Mod|Fun
import 1-Dim.AnyPoSet.Defs as AnyPoSet

module 1-Dim.PoSet.Def-Opers.Rep where

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
         (2vf @(v1 ~ v2) : Any.[Dup|R] (2~ [Fun]) 22A)
         (HM : [Mod] (A21 ~ A22)) where
  Rest : [Mod] (A11 ~ A12)
  Rest .↓ .M-ob (a11 ~ a12) = HM .M-ob (v1 .f-ob a11 ~ v2 .f-ob a12)
  Rest .is .lact _ (a11to × r) = HM .lact _ (v1 .f-to _ a11to × r)
  Rest .is .ract _ (r × a12to) = HM .ract _ (r × v2 .f-to _ a12to)

  -- (Cart)esian 2-cell
  Cart : [Mod|Fun] _ 2vf (Rest ~ HM)
  Cart .↓ _ = Any.Fun-Id _
