open import 0-Dim-qua
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Def-Opers.Mod
import 2-Dim.PoCat.Def-Types.is-Ob as PoCat
open import 2-Dim.PoCat.Def-Types-pub.is-Ob
import 2-Dim.PoQuiver.Def-Types.Ob as PoQuiver
open import 2-Dim.PoQuiver.Def-Types-pub.Ob

--
-- Mod-[Fun] satisfies axioms of [PoCat]
--
module 1-Dim.PoSet.Def-Opers.Mod-Fun where

module Mod where
  Qu : PoQuiver.[Ob]
  Qu .Ob = [Ob]
  Qu .Hom = Mod

  oper : PoCat.[oper] Qu
  oper .Id = Mod-Id
  oper .Mu = Mod-Mu

  prop : PoCat.[prop] Qu oper
  prop .Assoc-fw (ob1 ~ ob2 ~ ob3 ~ ob4) (R12 × R23 × R34) .↓ _ ((r12 ∙ r23) ∙ r34) = (r12 ∙ (r23 ∙ r34))
  prop .Assoc-bw (ob1 ~ ob2 ~ ob3 ~ ob4) (R12 × R23 × R34) .↓ _ (r12 ∙ (r23 ∙ r34)) = ((r12 ∙ r23) ∙ r34)
  prop .LUnit-fw (ob1 ~ ob2) R12 .↓ _ r12 = (ob1 .refl _ ∙ r12)
  prop .LUnit-bw (ob1 ~ ob2) R12 .↓ _ (1to ∙ r12) = R12 .lact _ (1to × r12)
  prop .RUnit-fw (ob1 ~ ob2) R12 .↓ _ r12 = (r12 ∙ ob2 .refl _)
  prop .RUnit-bw (ob1 ~ ob2) R12 .↓ _ (r12 ∙ 2to) = R12 .ract _ (r12 × 2to)
  prop .BUnit-fw ob .↓ _ to = (to ∙ ob .refl _)
  prop .BUnit-bw ob .↓ _ (1to ∙ 2to) = ob .tran _ (1to × 2to)
