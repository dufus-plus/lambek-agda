open import 0-Dim.!quali
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Def-Opers.Fun
import 2-Dim-Pre.PoSet-Qu.Def-Types.Obj as PoSet-Qu
open import 2-Dim-Pre.PoSet-Qu.Def-Types-pub.Obj
import 2-Dim.PoCat.Def-Types.is-Obj as PoCat
open import 2-Dim.PoCat.Def-Types-pub.is-Obj

--
-- Fun-[To] satisfies axioms of [PoCat]
--
module 1-Dim.PoSet.Def-Opers.Fun-To where

module Fun where
  Qu : PoSet-Qu.[Obj]
  Qu .Ob = [Ob] -- PoSet
  Qu .Hom = Fun

  has-oper : PoCat.[Obj-oper] Qu
  has-oper .Id = Fun-Id
  has-oper .Mu = Fun-Mu

  has-prop : PoCat.[Obj-prop] Qu has-oper
  has-prop .assoc-fw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) .↓ _ = ob4 .refl _
  has-prop .assoc-bw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) .↓ _ = ob4 .refl _
  has-prop .lunit-fw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  has-prop .lunit-bw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  has-prop .runit-fw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  has-prop .runit-bw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  has-prop .bunit-fw ob .↓ _ = ob .refl _
  has-prop .bunit-bw ob .↓ _ = ob .refl _
