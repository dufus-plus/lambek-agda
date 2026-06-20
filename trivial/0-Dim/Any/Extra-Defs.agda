open import 0-Dim.Prelude.!all
open import 0-Dim.Any.!quali

import 2-Dim-Pre.AnySet.Def-Types as AnySet
import 2-Dim-Pre.AnyPoSet.Def-Types as AnyPoSet
import 1-Dim.PoSet.Def-Types as PoSet
import 1-Dim.Set.Def-Types as Set
import 2-Dim.Quiver.Def-Types as Quiver
import 2-Dim.PoSet-Qu.Def-Types as PoSet-Qu
import 2-Dim.Cat.Def-Types as Cat
import 2-Dim.PoCat.Def-Types as PoCat
open import 1-Dim.Graph.Def-Types-pub
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.Set.Def-Types-pub
open import 2-Dim.Quiver.Def-Types-pub
open import 2-Dim.PoSet-Qu.Def-Types-pub
open import 2-Dim.Cat.Def-Types-pub
open import 2-Dim.PoCat.Def-Types-pub

--
-- categories comprised of types
--
module 0-Dim.Any.Extra-Defs where

--
-- define PoSet on [Any]
--
Any:PS : PoSet.[Ob]
Any:PS .It .El   = [Any]
Any:PS .It .To   = Any.[Fun]
Any:PS .is .refl = Any.Fun-Id
Any:PS .is .tran = Any.Fun-Mu

--
-- define Cat on Any.[Fun]
--
module _ (AB @ (A > B) : [2~] Any.[Ob]) where
  Fun:S : Set.[Ob]
  Fun:S .It .El = Any.[Fun] AB
  Fun:S .It .To = Any.Fun-[Id] AB
  Fun:S .is .refl _ a = ≡.refl
  Fun:S .is .symm _ (fto) a = ≡.symm (fto a)
  Fun:S .is .tran _ (fto12 × fto23) a = ≡.tran (fto12 a × fto23 a)

Fun:S-Id : AnySet.Rel-[0-Fun] _ (! > Fun:S)
Fun:S-Id _ = Any.Fun-Id _

Fun:S-Mu : AnySet.Rel-[2-Fun] _ ((Fun:S × Fun:S) > Fun:S)
Fun:S-Mu _ .↓ .f-el = Any.Fun-Mu _
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
  is-prop .assoc-fw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) _ = ≡ _
  is-prop .assoc-bw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) _ = ≡ _
  is-prop .lunit-fw (ob1 ~ ob2) f12 _ = ≡ _
  is-prop .lunit-bw (ob1 ~ ob2) f12 _ = ≡ _
  is-prop .runit-fw (ob1 ~ ob2) f12 _ = ≡ _
  is-prop .runit-bw (ob1 ~ ob2) f12 _ = ≡ _
  is-prop .bunit-fw ob _ = ≡ _
  is-prop .bunit-bw ob _ = ≡ _

Fun:C : Cat.[Obj]
Fun:C .It   = Fun:Q
Fun:C .oper = Fun:Q.is-oper
Fun:C .prop = Fun:Q.is-prop
-- yes, it's catoid

--
-- define PoCat on Any.[Rel]
--
module _ (AB @ (A > B) : [2~] Any.[Ob]) where
  Rel:PS : PoSet.[Ob]
  Rel:PS .It .El   = Any.[Rel] AB
  Rel:PS .It .To   = Any.Rel-[Fun] AB
  Rel:PS .is .refl = Any.Rel-Fun-Id AB
  Rel:PS .is .tran = Any.Rel-Fun-Mu AB

Rel:PS-Id : AnyPoSet.Rel-[0-Fun] _ (! > Rel:PS)
Rel:PS-Id A = Any.Rel-Id A

Rel:PS-Mu : AnyPoSet.Rel-[2-Fun] _ ((Rel:PS × Rel:PS) > Rel:PS)
Rel:PS-Mu _ .↓ .f-el = Any.Rel-Mu _
Rel:PS-Mu _ .↓ .f-to _ (fab × fbc) _ (mab ∙ mbc) = fab _ mab ∙ fbc _ mbc

Rel:PQ : PoSet-Qu.[Obj]
Rel:PQ .Ob = Any.[Ob]
Rel:PQ .Hom = Rel:PS

module Rel:PQ where
  is-oper : PoCat.[oper] Rel:PQ
  is-oper .Id = Rel:PS-Id
  is-oper .Mu = Rel:PS-Mu

  is-prop : PoCat.[prop] Rel:PQ is-oper
  is-prop .assoc-fw _ _ _ ((r12 ∙ r23) ∙ r34) = (r12 ∙ (r23 ∙ r34))
  is-prop .assoc-bw _ _ _ (r12 ∙ (r23 ∙ r34)) = ((r12 ∙ r23) ∙ r34)
  is-prop .lunit-fw _ _ _ r12 = (≡ _ ∙ r12)
  is-prop .lunit-bw _ _ _ (≡ _ ∙ r12) = r12
  is-prop .runit-fw _ _ _ r12 = (r12 ∙ ≡ _)
  is-prop .runit-bw _ _ _ (r12 ∙ ≡ _) = r12
  is-prop .bunit-fw _ _ (≡ _) = (≡ _ ∙ ≡ _)
  is-prop .bunit-bw _ _ (≡ _ ∙ ≡ _) = (≡ _)

Rel:PC : Cat.[Obj]
Rel:PC .It   = Fun:Q
Rel:PC .oper = Fun:Q.is-oper
Rel:PC .prop = Fun:Q.is-prop
-- yes, it's pocatoid

-- TODO: 3 DblCat: Fun|Fun Rel|Fun Rel|Rel
