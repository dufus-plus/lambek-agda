open import 0-Dim.Prelude
open import 0-Dim.Any-qua
import 1-Dim.AnySet.Def-Types as AnySet
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet
open import 1-Dim.Graph.Def-Types-pub
import 1-Dim.PoSet.Def-Types as PoSet
open import 1-Dim.PoSet.Def-Types-pub
import 1-Dim.Set.Def-Types as Set
open import 1-Dim.Set.Def-Types-pub
import 2-Dim.Quiver.Def-Types as Quiver
open import 2-Dim.Quiver.Def-Types-pub
import 2-Dim.PoQuiver.Def-Types as PoQuiver
open import 2-Dim.PoQuiver.Def-Types-pub
import 2-Dim.Cat.Def-Types as Cat
open import 2-Dim.Cat.Def-Types-pub
import 2-Dim.PoCat.Def-Types as PoCat
open import 2-Dim.PoCat.Def-Types-pub

module 0-Dim.Any.Extra where

-- poset of propositions
Any:PS : PoSet.[Ob]
Any:PS .It .Ob = Any.[Ob]
Any:PS .It .To = Any.[Fun]
Any:PS .is .refl = Any.Fun-Id
Any:PS .is .tran = Any.Fun-Mu

module _ (AB @ (A > B) : [2~] Any.[Ob]) where
  Fun:S : Set.[Ob]
  Fun:S .It .Ob = Any.[Fun] AB
  Fun:S .It .To = Any.Fun-[Id] AB
  Fun:S .is .refl _ a = ≡.refl
  Fun:S .is .symm _ (- fto) a = ≡.symm (fto a)
  Fun:S .is .tran _ (fto12 × fto23) a = ≡.tran (fto12 a × fto23 a)

module _ (AB @ (A > B) : [2~] Any.[Ob]) where
  Fun:PS : PoSet.[Ob]
  Fun:PS .It .Ob = Any.[Fun] AB
  Fun:PS .It .To = Any.Fun-[Id] AB
  Fun:PS .is .refl _ a = ≡.refl
  Fun:PS .is .tran _ (fto12 × fto23) a = ≡.tran (fto12 a × fto23 a)

Fun:S-Id : AnySet.Rel-[0Fun] _ (! > Fun:S)
Fun:S-Id _ = ⑴

Fun:S-Mu : AnySet.Rel-[2Fun] _ ((Fun:S × Fun:S) > Fun:S)
Fun:S-Mu _ .↓ .f-ob (fab × fbc) = fab ∘ fbc
Fun:S-Mu _ .↓ .f-to ((fab × fbc) ~ (gab × gbc)) (fidab × fidbc) a =
  ≡.tran (≡.cong fbc (fidab a) × fidbc (gab a))

Fun:PS-Id : AnyPoSet.Rel-[0Fun] _ (! > Fun:PS)
Fun:PS-Id _ = ⑴

Fun:PS-Mu : AnyPoSet.Rel-[2Fun] _ ((Fun:PS × Fun:PS) > Fun:PS)
Fun:PS-Mu _ .↓ .f-ob (fab × fbc) = fab ∘ fbc
Fun:PS-Mu _ .↓ .f-to ((fab × fbc) ~ (gab × gbc)) (fidab × fidbc) a =
  ≡.tran (≡.cong fbc (fidab a) × fidbc (gab a))

module Fun:S where
  Qu : Quiver.[Ob]
  Qu .Ob = Any.[Ob]
  Qu .Hom = Fun:S

  Qu-oper : Cat.[oper] Qu
  Qu-oper .Id = Fun:S-Id
  Qu-oper .Mu = Fun:S-Mu

  Qu-prop : Cat.[prop] Qu Qu-oper
  Qu-prop .Assoc-fw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) _ = ≡ _
  Qu-prop .Assoc-bw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) _ = ≡ _
  Qu-prop .LUnit-fw (ob1 ~ ob2) f12 _ = ≡ _
  Qu-prop .LUnit-bw (ob1 ~ ob2) f12 _ = ≡ _
  Qu-prop .RUnit-fw (ob1 ~ ob2) f12 _ = ≡ _
  Qu-prop .RUnit-bw (ob1 ~ ob2) f12 _ = ≡ _
  Qu-prop .BUnit-fw ob _ = ≡ _
  Qu-prop .BUnit-bw ob _ = ≡ _

module Fun:PS where
  Qu : PoQuiver.[Ob]
  Qu .Ob = Any.[Ob]
  Qu .Hom = Fun:PS

  Qu-oper : PoCat.[oper] Qu
  Qu-oper .Id = Fun:PS-Id
  Qu-oper .Mu = Fun:PS-Mu

  Qu-prop : PoCat.[prop] Qu Qu-oper
  Qu-prop .Assoc-fw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) _ = ≡ _
  Qu-prop .Assoc-bw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) _ = ≡ _
  Qu-prop .LUnit-fw (ob1 ~ ob2) f12 _ = ≡ _
  Qu-prop .LUnit-bw (ob1 ~ ob2) f12 _ = ≡ _
  Qu-prop .RUnit-fw (ob1 ~ ob2) f12 _ = ≡ _
  Qu-prop .RUnit-bw (ob1 ~ ob2) f12 _ = ≡ _
  Qu-prop .BUnit-fw ob _ = ≡ _
  Qu-prop .BUnit-bw ob _ = ≡ _

Fun:C : Cat.[Ob]
Fun:C .It   = Fun:S.Qu
Fun:C .oper = Fun:S.Qu-oper
Fun:C .prop = Fun:S.Qu-prop

Fun:PC : PoCat.[Ob]
Fun:PC .It   = Fun:PS.Qu
Fun:PC .oper = Fun:PS.Qu-oper
Fun:PC .prop = Fun:PS.Qu-prop

-- TODO DblCat
