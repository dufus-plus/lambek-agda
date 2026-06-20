open import 0-Dim.!quali
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Def-Opers.Mod
import 2-Dim.PoCat.Def-Types.is-Obj as PoCat
open import 2-Dim.PoCat.Def-Types-pub.is-Obj
import 2-Dim.PoSet-Quiver.Def-Types.Obj as PoSet-Quiver
open import 2-Dim.PoSet-Quiver.Def-Types-pub.Obj

--
-- Mod-[Fun] satisfies axioms of [PoCat]
--
module 1-Dim.PoSet.Def-Opers.Mod-Fun where

module Mod where
  Qu : PoSet-Quiver.[Obj]
  Qu .Ob = [Ob]
  Qu .Hom = Mod

  has-oper : PoCat.[Obj-oper] Qu
  has-oper .Id = Mod-Id
  has-oper .Mu = Mod-Mu

  has-prop : PoCat.[Obj-prop] Qu has-oper
  has-prop .assoc-fw (ob1 ~ ob2 ~ ob3 ~ ob4) (R12 × R23 × R34) .↓ _ ((r12 ∙ r23) ∙ r34) = (r12 ∙ (r23 ∙ r34))
  has-prop .assoc-bw (ob1 ~ ob2 ~ ob3 ~ ob4) (R12 × R23 × R34) .↓ _ (r12 ∙ (r23 ∙ r34)) = ((r12 ∙ r23) ∙ r34)
  has-prop .lunit-fw (ob1 ~ ob2) R12 .↓ _ r12 = (ob1 .refl _ ∙ r12)
  has-prop .lunit-bw (ob1 ~ ob2) R12 .↓ _ (1to ∙ r12) = R12 .lact _ (1to × r12)
  has-prop .runit-fw (ob1 ~ ob2) R12 .↓ _ r12 = (r12 ∙ ob2 .refl _)
  has-prop .runit-bw (ob1 ~ ob2) R12 .↓ _ (r12 ∙ 2to) = R12 .ract _ (r12 × 2to)
  has-prop .bunit-fw ob .↓ _ to = (to ∙ ob .refl _)
  has-prop .bunit-bw ob .↓ _ (1to ∙ 2to) = ob .tran _ (1to × 2to)
