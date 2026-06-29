open import 0-Dim.!quali
open import 1-Dim.Graph.Def-Types
open import 1-Dim.Graph.Def-Types-pub
import 2-Dim-Pre.Matr.Def-Types as Matr
import 1-Dim.PoSet.Def-Types as PoSet
open import 1-Dim.PoSet.Def-Types-pub

module 1-Dim.Graph.Def-Opers.Mod where

module _ (AB : [2~] [Ob]) where
  Mod : PoSet.[Ob]
  Mod .It .El = [Mod] AB
  Mod .It .To = Mod-[Fun] _
  Mod .is .refl _ .↓ _ = ⑴
  Mod .is .tran _ (to12 × to23) .↓ _ = to12 .↓ _ ∘ to23 .↓ _

Mod-Id : Matr.PoSet-[0-Fun] _ (! > Mod)
Mod-Id A .M-ob = A .To

Mod-Mu : Matr.PoSet-[2-Fun] _ ((Mod × Mod) > Mod)
Mod-Mu _ .↓ .f-el (Rab × Rbc) .M-ob = (Rab .M-ob) [∙] (Rbc .M-ob)
Mod-Mu _ .↓ .f-to _ (toab × tobc) .↓ _ (mab ∙ mbc) =
  toab .↓ _ mab ∙ tobc .↓ _ mbc
