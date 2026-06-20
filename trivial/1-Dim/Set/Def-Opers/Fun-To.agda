open import 0-Dim.!quali
open import 1-Dim.Set.Def-Types
open import 1-Dim.Set.Def-Types-pub
open import 1-Dim.Set.Def-Opers.Fun
import 2-Dim.Quiver.Def-Types.Obj as Quiver
open import 2-Dim.Quiver.Def-Types-pub.Obj
import 2-Dim-Pre.PoSet-Qu.Def-Types.Obj as PoSet-Qu
open import 2-Dim-Pre.PoSet-Qu.Def-Types-pub.Obj
import 2-Dim.Cat.Def-Types.is-Obj as Cat
open import 2-Dim.Cat.Def-Types-pub.is-Obj
import 2-Dim.PoCat.Def-Types.is-Obj as PoCat
open import 2-Dim.PoCat.Def-Types-pub.is-Obj

--
-- Fun-[To] satisfies axioms of [Cat]
--
module 1-Dim.Set.Def-Opers.Fun-To where

Fun:Q : Quiver.[Obj]
Fun:Q .Ob = [Ob]
Fun:Q .Hom = Fun

module Fun:C where
  oper : Cat.[oper] Fun:Q
  oper .Id = Fun-Id
  oper .Mu = Fun-Mu

  prop : Cat.[prop] Fun:Q oper
  prop .assoc-fw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) .↓ _ = ob4 .refl _
  prop .assoc-bw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) .↓ _ = ob4 .refl _
  prop .lunit-fw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .lunit-bw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .runit-fw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .runit-bw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .bunit-fw ob .↓ _ = ob .refl _
  prop .bunit-bw ob .↓ _ = ob .refl _
