open import 0-Dim
open import 1-Dim.Set.Defs
open import 1-Dim.Set.Oper.Mod
import 2-Dim.PoCat.Defs.is as PoCat
import 2-Dim.PoSet-Graph.Defs.Ob as PoSet-Graph

--
-- Mod-[Fun] satisfies axioms of [PoCat]
--
module 1-Dim.Set.Oper.Mod-Fun where

open PoSet-Graph.[Ob]
open PoCat.[oper]
open PoCat.[prop]
open Mod-[Fun]
open [Ob]
open [Mod]

module Mod where
  Graph : PoSet-Graph.[Ob]
  Graph .Ob = [Ob] -- PoSet
  Graph .Hom = Mod

  oper : PoCat.[oper] Graph
  oper .Id = Mod-Id
  oper .Mu = Mod-Mu

  prop : PoCat.[prop] Graph oper
  prop .Mu-Assoc-fw (ob1 ~ ob2 ~ ob3 ~ ob4) (R12 × R23 × R34) .↓ _ ((r12 ∙ r23) ∙ r34) = (r12 ∙ (r23 ∙ r34))
  prop .Mu-Assoc-bw (ob1 ~ ob2 ~ ob3 ~ ob4) (R12 × R23 × R34) .↓ _ (r12 ∙ (r23 ∙ r34)) = ((r12 ∙ r23) ∙ r34)
  prop .Id-LUnit-fw (ob1 ~ ob2) R12 .↓ _ r12 = (ob1 .refl _ ∙ r12)
  prop .Id-LUnit-bw (ob1 ~ ob2) R12 .↓ _ (1to ∙ r12) = R12 .lact _ (1to × r12)
  prop .Id-RUnit-fw (ob1 ~ ob2) R12 .↓ _ r12 = (r12 ∙ ob2 .refl _)
  prop .Id-RUnit-bw (ob1 ~ ob2) R12 .↓ _ (r12 ∙ 2to) = R12 .ract _ (r12 × 2to)
