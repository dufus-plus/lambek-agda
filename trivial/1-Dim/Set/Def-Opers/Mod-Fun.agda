open import 0-Dim.!quali
open import 1-Dim.Set.Def-Types
open import 1-Dim.Set.Def-Types-pub
open import 1-Dim.Set.Def-Opers.Mod
import 2-Dim.PoCat.Def-Types.is-Obj as PoCat
open import 2-Dim.PoCat.Def-Types-pub.is-Obj
import 2-Dim.PoSet-Qu.Def-Types as PoSet-Qu
open import 2-Dim.PoSet-Qu.Def-Types-pub

--
-- Mod-[Fun] satisfies axioms of [PoCat]
--
module 1-Dim.Set.Def-Opers.Mod-Fun where

Mod:PQ : PoSet-Qu.[Obj]
Mod:PQ .Ob = [Ob] -- Set
Mod:PQ .Hom = Mod

module Mod:PC where
  oper : PoCat.[oper] Mod:PQ
  oper .Id = Mod-Id
  oper .Mu = Mod-Mu

  prop : PoCat.[prop] Mod:PQ oper
  prop .assoc-fw 4ob 3R .↓ _ ((r12 ∙ r23) ∙ r34) = (r12 ∙ (r23 ∙ r34))
  prop .assoc-bw 4ob 3R .↓ _ (r12 ∙ (r23 ∙ r34)) = ((r12 ∙ r23) ∙ r34)
  prop .lunit-fw (ob1 ~ ob2) R12 .↓ _ r12 = (ob1 .refl _ ∙ r12)
  prop .lunit-bw (ob1 ~ ob2) R12 .↓ _ (1to ∙ r12) = R12 .lact _ (1to × r12)
  prop .runit-fw (ob1 ~ ob2) R12 .↓ _ r12 = (r12 ∙ ob2 .refl _)
  prop .runit-bw (ob1 ~ ob2) R12 .↓ _ (r12 ∙ 2to) = R12 .ract _ (r12 × 2to)
  prop .bunit-fw ob .↓ _ to = (to ∙ ob .refl _)
  prop .bunit-bw ob .↓ _ (1to ∙ 2to) = ob .tran _ (1to × 2to)
