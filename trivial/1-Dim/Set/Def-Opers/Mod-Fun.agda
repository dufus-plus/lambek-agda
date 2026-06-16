open import 0-Dim.!quali
open import 1-Dim.Set.Def-Types
open import 1-Dim.Set.Def-Types-pub
open import 1-Dim.Set.Def-Opers.Mod
import 2-Dim.PoCat.Def-Types.is-Ob as PoCat
open import 2-Dim.PoCat.Def-Types-pub.is-Ob
import 2-Dim.PoQuiver.Def-Types as PoQuiver
open import 2-Dim.PoQuiver.Def-Types-pub

--
-- Mod-[Fun] satisfies axioms of [PoCat]
--
module 1-Dim.Set.Def-Opers.Mod-Fun where

module Mod where
  Quiver : PoQuiver.[Ob]
  Quiver .Ob = [Ob] -- Set
  Quiver .Hom = Mod

  oper : PoCat.[oper] Quiver
  oper .Id = Mod-Id
  oper .Mu = Mod-Mu

  prop : PoCat.[prop] Quiver oper
  prop .Assoc-fw 4ob 3R .↓ _ ((r12 ∙ r23) ∙ r34) = (r12 ∙ (r23 ∙ r34))
  prop .Assoc-bw 4ob 3R .↓ _ (r12 ∙ (r23 ∙ r34)) = ((r12 ∙ r23) ∙ r34)
  prop .LUnit-fw (ob1 ~ ob2) R12 .↓ _ r12 = (ob1 .refl _ ∙ r12)
  prop .LUnit-bw (ob1 ~ ob2) R12 .↓ _ (1to ∙ r12) = R12 .lact _ (1to × r12)
  prop .RUnit-fw (ob1 ~ ob2) R12 .↓ _ r12 = (r12 ∙ ob2 .refl _)
  prop .RUnit-bw (ob1 ~ ob2) R12 .↓ _ (r12 ∙ 2to) = R12 .ract _ (r12 × 2to)
  prop .BUnit-fw ob .↓ _ to = (to ∙ ob .refl _)
  prop .BUnit-bw ob .↓ _ (1to ∙ 2to) = ob .tran _ (1to × 2to)
