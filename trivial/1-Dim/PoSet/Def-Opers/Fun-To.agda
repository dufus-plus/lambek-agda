open import 0-Dim.!quali
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Def-Opers.Fun
import 2-Dim.PoQuiver.Def-Types.Obj as PoQuiver
open import 2-Dim.PoQuiver.Def-Types-pub.Obj
import 2-Dim.PoCat.Def-Types.is-Ob as PoCat
open import 2-Dim.PoCat.Def-Types-pub.is-Ob

--
-- Fun-[To] satisfies axioms of [PoCat]
--
module 1-Dim.PoSet.Def-Opers.Fun-To where

module Fun where
  Qu : PoQuiver.[Ob]
  Qu .Ob = [Ob] -- PoSet
  Qu .Hom = Fun

  oper : PoCat.[oper] Qu
  oper .Id = Fun-Id
  oper .Mu = Fun-Mu

  prop : PoCat.[prop] Qu oper
  prop .Assoc-fw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) .↓ _ = ob4 .refl _
  prop .Assoc-bw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) .↓ _ = ob4 .refl _
  prop .LUnit-fw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .LUnit-bw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .RUnit-fw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .RUnit-bw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .BUnit-fw ob .↓ _ = ob .refl _
  prop .BUnit-bw ob .↓ _ = ob .refl _
