open import 0-Dim.!quali
import 1-Dim.Graph.Def-Types as Graph
open import 1-Dim.Graph.Def-Types-pub
import 1-Dim.PoSet.Def-Types as PoSet
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.Set.Def-Types
open import 1-Dim.Set.Def-Types-pub
import 2-Dim-Pre.Matr.Def-Types as Matr

module 1-Dim.Set.Def-Opers.Mod where

module _ (AB : [2~] [Ob]) where
  Mod : PoSet.[Ob]
  Mod .It .El = [Mod] AB
  Mod .It .To = Mod-[Fun] _
  Mod .is .refl M .↓ _ = ⑴
  Mod .is .tran _ (rto12 × rto23) .↓ _ = rto12 .↓ _ ∘ rto23 .↓ _

Mod-Id : Matr.PoSet-[0-Fun] _ (! > Mod)
Mod-Id A .It .M-ob = A .To
Mod-Id A .is .lact = A .tran
Mod-Id A .is .ract = A .tran

Mod-Mu : Matr.PoSet-[2-Fun] _ ((Mod × Mod) > Mod)
Mod-Mu _ .↓ .f-el (Rab × Rbc) .It .M-ob = (Rab .M-ob) [∙] (Rbc .M-ob)
Mod-Mu _ .↓ .f-el (Rab × Rbc) .is .lact _ (aeq12 × (rab ∙ rbc)) = (Rab .lact _ (aeq12 × rab)) ∙ rbc
Mod-Mu _ .↓ .f-el (Rab × Rbc) .is .ract _ ((rab ∙ rbc) × ceq12) = rab ∙ (Rbc .ract _ (rbc × ceq12))
Mod-Mu _ .↓ .f-to _ (toab × tobc) .↓ ac (mab ∙ mbc) =
  toab .↓ _ mab ∙ tobc .↓ _ mbc
