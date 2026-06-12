open import 0-Dim
open import 1-Dim.Graph
open import 1-Dim.PoSet.Def-Types.Ob
open import 1-Dim.PoSet.Def-Types.Fun
open import 1-Dim.PoSet.Def-Types.Mod
open import 1-Dim.PoSet.Def-Types.Mod-Fun
open import 1-Dim.PoSet.Def-Types-pub.Ob
open import 1-Dim.PoSet.Def-Types-pub.Fun
open import 1-Dim.PoSet.Def-Types-pub.Mod
open import 1-Dim.PoSet.Def-Types-pub.Mod-Fun
open import 1-Dim.PoSet.Gens.Mod
import 1-Dim.AnyPoSet.Defs as AnyPoSet

module 1-Dim.PoSet.Def-Opers.Mod where

open Graph.[Ob]
open Graph.[Mod]
open Graph.[Fun]

Mod-Id : AnyPoSet.Rel-[0Fun] _ (! > Mod)
Mod-Id A .↓ .M-ob = A .To
Mod-Id A .is .lact = A .tran
Mod-Id A .is .ract = A .tran

Mod-Mu : AnyPoSet.Rel-[2Fun] _ ((Mod × Mod) > Mod)
Mod-Mu _ .↓ .f-ob (Rab × Rbc) .↓ .M-ob = (Rab .M-ob) [∙] (Rbc .M-ob)
Mod-Mu _ .↓ .f-ob (Rab × Rbc) .is .lact _ (aeq12 × (rab ∙ rbc)) = (Rab .lact _ (aeq12 × rab)) ∙ rbc
Mod-Mu _ .↓ .f-ob (Rab × Rbc) .is .ract _ ((rab ∙ rbc) × ceq12) = rab ∙ (Rbc .ract _ (rbc × ceq12))
Mod-Mu _ .↓ .f-to _ (toab × tobc) .↓ ac (mab ∙ mbc) =
  toab .↓ _ mab ∙ tobc .↓ _ mbc
