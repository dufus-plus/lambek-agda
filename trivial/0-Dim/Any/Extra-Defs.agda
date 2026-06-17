open import 0-Dim.Prelude.!all
open import 0-Dim.Any.!quali

import 1-Dim.AnySet.Def-Types as AnySet
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet
import 1-Dim.PoSet.Def-Types as PoSet
import 1-Dim.Set.Def-Types as Set
import 2-Dim.Quiver.Def-Types as Quiver
import 2-Dim.PoQuiver.Def-Types as PoQuiver
import 2-Dim.Cat.Def-Types as Cat
import 2-Dim.PoCat.Def-Types as PoCat
open import 1-Dim.Graph.Def-Types-pub
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.Set.Def-Types-pub
open import 2-Dim.Quiver.Def-Types-pub
open import 2-Dim.PoQuiver.Def-Types-pub
open import 2-Dim.Cat.Def-Types-pub
open import 2-Dim.PoCat.Def-Types-pub

--
-- categories comprised of types
--
module 0-Dim.Any.Extra-Defs where

-- poset of (relevant) propositions
Any:PS : PoSet.[Ob]
Any:PS .It .El   = Any.[Ob]
Any:PS .It .To   = Any.[Fun]
Any:PS .is .refl = Any.Fun-Id
Any:PS .is .tran = Any.Fun-Mu

module _ (AB @ (A > B) : [2~] Any.[Ob]) where
  Rel:PS : PoSet.[Ob]
  Rel:PS .It .El   = Any.[Rel] AB
  Rel:PS .It .To   = Any.Rel-[Fun] AB
  Rel:PS .is .refl = Any.Rel-Fun-Id AB
  Rel:PS .is .tran = Any.Rel-Fun-Mu AB

module _ (AB @ (A > B) : [2~] Any.[Ob]) where
  Fun:S : Set.[Ob]
  Fun:S .It .El = Any.[Fun] AB
  Fun:S .It .To = Any.Fun-[Id] AB
  Fun:S .is .refl _ a = ≡.refl
  Fun:S .is .symm _ (fto) a = ≡.symm (fto a)
  Fun:S .is .tran _ (fto12 × fto23) a = ≡.tran (fto12 a × fto23 a)

Fun:S-Id : AnySet.Rel-[0-Fun] _ (! > Fun:S)
Fun:S-Id _ = ⑴

Fun:S-Mu : AnySet.Rel-[2-Fun] _ ((Fun:S × Fun:S) > Fun:S)
Fun:S-Mu _ .↓ .f-el (fab × fbc) = fab ∘ fbc
Fun:S-Mu _ .↓ .f-to ((fab × fbc) ~ (gab × gbc)) (fidab × fidbc) a =
  ≡.tran (≡.cong fbc (fidab a) × fidbc (gab a))

Fun:Q : Quiver.[Obj]
Fun:Q .Ob = Any.[Ob]
Fun:Q .Hom = Fun:S

module Fun:Q where
  is-oper : Cat.[oper] Fun:Q
  is-oper .Id = Fun:S-Id
  is-oper .Mu = Fun:S-Mu

  is-prop : Cat.[prop] Fun:Q is-oper
  is-prop .Assoc-fw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) _ = ≡ _
  is-prop .Assoc-bw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) _ = ≡ _
  is-prop .LUnit-fw (ob1 ~ ob2) f12 _ = ≡ _
  is-prop .LUnit-bw (ob1 ~ ob2) f12 _ = ≡ _
  is-prop .RUnit-fw (ob1 ~ ob2) f12 _ = ≡ _
  is-prop .RUnit-bw (ob1 ~ ob2) f12 _ = ≡ _
  is-prop .BUnit-fw ob _ = ≡ _
  is-prop .BUnit-bw ob _ = ≡ _

Fun:C : Cat.[Obj]
Fun:C .It   = Fun:Q
Fun:C .oper = Fun:Q.is-oper
Fun:C .prop = Fun:Q.is-prop

-- TODO: 3 DblCat: Fun|Fun Rel|Fun Rel|Rel
