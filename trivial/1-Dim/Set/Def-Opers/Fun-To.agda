open import 0-Dim-qua
open import 1-Dim.Set.Def-Types
open import 1-Dim.Set.Def-Types-pub
open import 1-Dim.Set.Def-Opers.Fun
import 2-Dim.Quiver.Def-Types.Ob as Quiver
open import 2-Dim.Quiver.Def-Types-pub.Ob
import 2-Dim.Cat.Def-Types.is-Ob as Cat
open import 2-Dim.Cat.Def-Types-pub.is-Ob

--
-- Fun-[To] satisfies axioms of [Cat]
--
module 1-Dim.Set.Def-Opers.Fun-To where

module Fun where
  Quiver : Quiver.[Ob]
  Quiver .Ob = [Ob]
  Quiver .Hom = Fun

  oper : Cat.[oper] Quiver
  oper .Id = Fun-Id
  oper .Mu = Fun-Mu

  prop : Cat.[prop] Quiver oper
  prop .Assoc-fw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) .↓ _ = ob4 .refl _
  prop .Assoc-bw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) .↓ _ = ob4 .refl _
  prop .LUnit-fw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .LUnit-bw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .RUnit-fw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .RUnit-bw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .BUnit-fw ob .↓ _ = ob .refl _
  prop .BUnit-bw ob .↓ _ = ob .refl _
