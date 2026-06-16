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
Any:PS .It .Ob   = Any.[Ob]
Any:PS .It .To   = Any.[Fun]
Any:PS .is .refl = Any.Fun-Id
Any:PS .is .tran = Any.Fun-Mu

module _ (AB @ (A > B) : [2~] Any.[Ob]) where
  Rel:PS : PoSet.[Ob]
  Rel:PS .It .Ob   = Any.[Rel] AB
  Rel:PS .It .To   = Any.Rel-[Fun] AB
  Rel:PS .is .refl = Any.Rel-Fun-Id AB
  Rel:PS .is .tran = Any.Rel-Fun-Mu AB

module _ (AB @ (A > B) : [2~] Any.[Ob]) where
  Fun:Q : Set.[Ob]
  Fun:Q .It .Ob = Any.[Fun] AB
  Fun:Q .It .To = Any.Fun-[Id] AB
  Fun:Q .is .refl _ a = ≡.refl
  Fun:Q .is .symm _ (- fto) a = ≡.symm (fto a)
  Fun:Q .is .tran _ (fto12 × fto23) a = ≡.tran (fto12 a × fto23 a)

module _ (AB @ (A > B) : [2~] Any.[Ob]) where
  Fun:PQ : PoSet.[Ob]
  Fun:PQ .It .Ob = Any.[Fun] AB
  Fun:PQ .It .To = Any.Fun-[Id] AB
  Fun:PQ .is .refl _ a = ≡.refl
  Fun:PQ .is .tran _ (fto12 × fto23) a = ≡.tran (fto12 a × fto23 a)

Fun:Q-Id : AnySet.Rel-[0Fun] _ (! > Fun:Q)
Fun:Q-Id _ = ⑴

Fun:Q-Mu : AnySet.Rel-[2Fun] _ ((Fun:Q × Fun:Q) > Fun:Q)
Fun:Q-Mu _ .↓ .f-ob (fab × fbc) = fab ∘ fbc
Fun:Q-Mu _ .↓ .f-to ((fab × fbc) ~ (gab × gbc)) (fidab × fidbc) a =
  ≡.tran (≡.cong fbc (fidab a) × fidbc (gab a))

Fun:PQ-Id : AnyPoSet.Rel-[0Fun] _ (! > Fun:PQ)
Fun:PQ-Id _ = ⑴

Fun:PQ-Mu : AnyPoSet.Rel-[2Fun] _ ((Fun:PQ × Fun:PQ) > Fun:PQ)
Fun:PQ-Mu _ .↓ .f-ob (fab × fbc) = fab ∘ fbc
Fun:PQ-Mu _ .↓ .f-to ((fab × fbc) ~ (gab × gbc)) (fidab × fidbc) a =
  ≡.tran (≡.cong fbc (fidab a) × fidbc (gab a))

module Fun:Q where
  Qu : Quiver.[Ob]
  Qu .Ob = Any.[Ob]
  Qu .Hom = Fun:Q

  is-oper : Cat.[oper] Qu
  is-oper .Id = Fun:Q-Id
  is-oper .Mu = Fun:Q-Mu

  is-prop : Cat.[prop] Qu is-oper
  is-prop .Assoc-fw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) _ = ≡ _
  is-prop .Assoc-bw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) _ = ≡ _
  is-prop .LUnit-fw (ob1 ~ ob2) f12 _ = ≡ _
  is-prop .LUnit-bw (ob1 ~ ob2) f12 _ = ≡ _
  is-prop .RUnit-fw (ob1 ~ ob2) f12 _ = ≡ _
  is-prop .RUnit-bw (ob1 ~ ob2) f12 _ = ≡ _
  is-prop .BUnit-fw ob _ = ≡ _
  is-prop .BUnit-bw ob _ = ≡ _

module Fun:PQ where
  PQu : PoQuiver.[Ob]
  PQu .Ob = Any.[Ob]
  PQu .Hom = Fun:PQ

  is-oper : PoCat.[oper] PQu
  is-oper .Id = Fun:PQ-Id
  is-oper .Mu = Fun:PQ-Mu

  is-prop : PoCat.[prop] PQu is-oper
  is-prop .Assoc-fw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) _ = ≡ _
  is-prop .Assoc-bw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) _ = ≡ _
  is-prop .LUnit-fw (ob1 ~ ob2) f12 _ = ≡ _
  is-prop .LUnit-bw (ob1 ~ ob2) f12 _ = ≡ _
  is-prop .RUnit-fw (ob1 ~ ob2) f12 _ = ≡ _
  is-prop .RUnit-bw (ob1 ~ ob2) f12 _ = ≡ _
  is-prop .BUnit-fw ob _ = ≡ _
  is-prop .BUnit-bw ob _ = ≡ _

Fun:C : Cat.[Ob]
Fun:C .It   = Fun:Q.Qu
Fun:C .oper = Fun:Q.is-oper
Fun:C .prop = Fun:Q.is-prop

Fun:PC : PoCat.[Ob]
Fun:PC .It   = Fun:PQ.PQu
Fun:PC .oper = Fun:PQ.is-oper
Fun:PC .prop = Fun:PQ.is-prop

-- TODO: 3 DblCat: Fun|Fun Rel|Fun Rel|Rel
