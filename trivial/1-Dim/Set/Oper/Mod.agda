open import 0-Dim
open import 1-Dim.Graph
import 1-Dim.PoSet.Defs as PoSet
open import 1-Dim.Set.Defs.Ob
open import 1-Dim.Set.Defs.Fun
open import 1-Dim.Set.Defs.Mod
open import 1-Dim.Set.Defs.Mod-Fun
import 1-Dim.AnyPoSet.Defs as AnyPoSet

module 1-Dim.Set.Oper.Mod where

open [is]
open [Ob]
open [Mod]
open [Fun]
open Mod-[Fun]
open [is-Mod]
open Graph.[Ob]
open Graph.[Mod]
open Graph.[Fun]
open PoSet.[Ob]
open PoSet.[is]
open PoSet.[Fun]

module _ (AB @ (A > B) : [2~] [Ob]) where
  Mod:PS : PoSet.[Ob]
  Mod:PS .↓ .Ob = [Mod] (A ~ B)
  Mod:PS .↓ .To = Mod-[Fun] _
  Mod:PS .is .refl M .↓ _ = ⑴
  Mod:PS .is .tran _ (rto12 × rto23) .↓ _ = rto12 .↓ _ ∘ rto23 .↓ _

Mod-Id : AnyPoSet.Rel-[0Fun] _ (! > Mod:PS)
Mod-Id A .↓ .M-ob = A .To
Mod-Id A .is .lact = A .tran
Mod-Id A .is .ract = A .tran

Mod-Mu : AnyPoSet.Rel-[2Fun] _ ((Mod:PS × Mod:PS) > Mod:PS)
Mod-Mu _ .↓ .f-ob (Rab × Rbc) .↓ .M-ob = (Rab .M-ob) [∙] (Rbc .M-ob)
Mod-Mu _ .↓ .f-ob (Rab × Rbc) .is .lact _ (aeq12 × (rab ∙ rbc)) = (Rab .lact _ (aeq12 × rab)) ∙ rbc
Mod-Mu _ .↓ .f-ob (Rab × Rbc) .is .ract _ ((rab ∙ rbc) × ceq12) = rab ∙ (Rbc .ract _ (rbc × ceq12))
Mod-Mu _ .↓ .f-to _ (toab × tobc) .↓ ac (mab ∙ mbc) =
  toab .↓ _ mab ∙ tobc .↓ _ mbc
