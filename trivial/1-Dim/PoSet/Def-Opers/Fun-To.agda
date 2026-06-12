open import 0-Dim
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Gens.Fun
open import 1-Dim.PoSet.Def-Opers.Fun
import 2-Dim.PoSet-Graph.Defs.Ob as PoSet-Graph
import 2-Dim.PoCat.Defs.is as PoCat

--
-- Fun-[To] satisfies axioms of [PoCat]
--
module 1-Dim.PoSet.Def-Opers.Fun-To where

open PoSet-Graph.[Ob]
open PoCat.[oper]
open PoCat.[prop]

module Fun where
  Graph : PoSet-Graph.[Ob]
  Graph .Ob = [Ob] -- PoSet
  Graph .Hom = Fun

  oper : PoCat.[oper] Graph
  oper .Id = Fun-Id
  oper .Mu = Fun-Mu

  prop : PoCat.[prop] Graph oper
  prop .Assoc-fw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) .↓ _ = ob4 .refl _
  prop .Assoc-bw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) .↓ _ = ob4 .refl _
  prop .LUnit-fw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .LUnit-bw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .RUnit-fw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .RUnit-bw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .BUnit-fw ob .↓ _ = ob .refl _
  prop .BUnit-bw ob .↓ _ = ob .refl _
