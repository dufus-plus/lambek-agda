open import 0-Dim.!quali
import 2-Dim-Pre.AnyPoSet.Def-Types as AnyPoSet
import 1-Dim.PoSet.Def-Types as PoSet
-- open import 1-Dim.PoSet.Def-Types-pub
import 2-Dim-Pre.PoSet-Qu.Def-Types.Obj as PoSet-Qu

module 2-Dim.PoCat.Def-Types.is-Obj where

open PoSet-Qu using (‼)

module _ (Qu : PoSet-Qu.[Obj]) where
  open PoSet-Qu.[Obj] Qu

  module :[Obj-oper]  where
    -- operations on Hom: (id)entity, (mu)ltiplication
    :Id = AnyPoSet.Rel-[0-Fun] _ (! > Hom)
    :Mu = AnyPoSet.Rel-[2-Fun] _ ((Hom × Hom) > Hom)

  record [Obj-oper] : [Any] where
    constructor ‼
    open :[Obj-oper]

    -- data:
    field Id : :Id
    field Mu : :Mu

    -- helpers:
    private module Mu (3ob : _) = PoSet.[Fun] (Mu 3ob)
    open Mu public
      using ()
      renaming
      ( f-el to Mu-el;
        f-to to Mu-to )

  module :[Obj-prop] (oper : [Obj-oper]) where
    open [Obj-oper] oper

    -- associativity of multiplication
    :assoc-fw =
      (4ob @(ob1 ~ ob2 ~ ob3 ~ ob4) : [4~] Ob)
      (3hom @(hom12 × hom23 × hom34):
        Hom-El (ob1 > ob2) [×] Hom-El (ob2 > ob3) [×] Hom-El (ob3 > ob4)) →
      Hom-To _ ( (Mu-el _ (Mu-el _ (hom12 × hom23) × hom34)) ~
                 (Mu-el _ (hom12 × Mu-el _ (hom23 × hom34))) )
    :assoc-bw =
      (4ob @(ob1 ~ ob2 ~ ob3 ~ ob4) : [4~] Ob)
      (3hom @(hom12 × hom23 × hom34):
        Hom-El (ob1 > ob2) [×] Hom-El (ob2 > ob3) [×] Hom-El (ob3 > ob4)) →
      Hom-To _ ( (Mu-el _ (hom12 × Mu-el _ (hom23 × hom34))) ~
                 (Mu-el _ (Mu-el _ (hom12 × hom23) × hom34)) )

    -- identity is (left,right) unit
    :lunit-fw =
      (2ob @(ob1 ~ ob2) : [2~] Ob) (hom12 : Hom-El (ob1 > ob2)) →
      Hom-To _ (hom12 ~ Mu-el _ (Id ob1 × hom12))
    :lunit-bw =
      (2ob @(ob1 ~ ob2) : [2~] Ob) (hom12 : Hom-El (ob1 > ob2)) →
      Hom-To _ (Mu-el _ (Id ob1 × hom12) ~ hom12)
    :runit-fw =
      (2ob @(ob1 ~ ob2) : [2~] Ob) (hom12 : Hom-El (ob1 > ob2)) →
      Hom-To _ (hom12 ~ Mu-el _ (hom12 × Id ob2))
    :runit-bw =
      (2ob @(ob1 ~ ob2) : [2~] Ob) (hom12 : Hom-El (ob1 > ob2)) →
      Hom-To _ (Mu-el _ (hom12 × Id ob2) ~ hom12)
    :bunit-fw =
      (ob : Ob) →
      Hom-To _ (Id ob ~ Mu-el _ (Id ob × Id ob))
    :bunit-bw =
      (ob : Ob) →
      Hom-To _ (Mu-el _ (Id ob × Id ob) ~ Id ob)

module _ (Qu : PoSet-Qu.[Obj]) (oper : [Obj-oper] Qu) where
  record [Obj-prop] : [Any] where
    constructor ‼
    open :[Obj-prop] Qu oper

    -- data:
    field assoc-fw : :assoc-fw
    field assoc-bw : :assoc-bw
    field lunit-fw : :lunit-fw
    field lunit-bw : :lunit-bw
    field runit-fw : :runit-fw
    field runit-bw : :runit-bw
    field bunit-fw : :bunit-fw
    field bunit-bw : :bunit-bw

record [is-Obj] (Ob : [Any]) : [Any] where
  constructor ‼

  -- data
  field Hom : PoSet-Qu.[is-Obj] Ob
  field oper : [Obj-oper] (‼ Ob Hom)
  field prop : [Obj-prop] (‼ Ob Hom) oper

  -- helpers:
  private module Hom (2ob : [2~] Ob) = PoSet.[Ob] (Hom 2ob)
  open Hom public
    using ()
    renaming
    ( It   to Hom-It;
      El   to Hom-El;
      To   to Hom-To;
      is   to Hom-is;
      refl to Hom-refl;
      tran to Hom-tran )
  open [Obj-oper] oper public
  open [Obj-prop] prop public

  Qu : PoSet-Qu.[Obj]
  Qu = ‼ Ob Hom
