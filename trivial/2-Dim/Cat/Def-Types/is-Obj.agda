open import 0-Dim.!quali
import 2-Dim-Pre.Matr.Def-Types as Matr
import 1-Dim.Set.Def-Types as Set
open import 1-Dim.Set.Def-Types-pub.Fun
open import 1-Dim.Graph.Def-Types-pub.Fun
import 2-Dim-Pre.Set-Qu.Def-Types.Obj as Set-Qu

module 2-Dim.Cat.Def-Types.is-Obj where

:Hom = Set-Qu.:Hom

module _ (Ob : [Any]) (Hom : :Hom Ob) where
  private module Hom (2ob : _) = Set.[Ob] (Hom 2ob)

  module :[Obj-oper]  where
    -- operations on Hom: (id)entity, (mu)ltiplication
    :Id = Matr.Set-[0-Fun] _ (! > Hom)
    :Mu = Matr.Set-[2-Fun] _ ((Hom × Hom) > Hom)

  record [Obj-oper] : [Any] where
    constructor ‼
    open :[Obj-oper]

    -- data:
    field Id : :Id
    field Mu : :Mu

    -- helpers:
    private module Mu (3ob : _) = Set.[Fun] (Mu 3ob)
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
        Hom.El (ob1 > ob2) [×] Hom.El (ob2 > ob3) [×] Hom.El (ob3 > ob4)) →
      Hom.To _ ( (Mu-el _ (Mu-el _ (hom12 × hom23) × hom34)) ~
                 (Mu-el _ (hom12 × Mu-el _ (hom23 × hom34))) )
    :assoc-bw =
      (4ob @(ob1 ~ ob2 ~ ob3 ~ ob4) : [4~] Ob)
      (3hom @(hom12 × hom23 × hom34):
        Hom.El (ob1 > ob2) [×] Hom.El (ob2 > ob3) [×] Hom.El (ob3 > ob4)) →
      Hom.To _ ( (Mu-el _ (hom12 × Mu-el _ (hom23 × hom34))) ~
                 (Mu-el _ (Mu-el _ (hom12 × hom23) × hom34)) )

    -- identity is (left,right) unit
    :lunit-fw =
      (2ob @(ob1 ~ ob2) : [2~] Ob) (hom12 : Hom.El (ob1 > ob2)) →
      Hom.To _ (hom12 ~ Mu-el _ (Id ob1 × hom12))
    :lunit-bw =
      (2ob @(ob1 ~ ob2) : [2~] Ob) (hom12 : Hom.El (ob1 > ob2)) →
      Hom.To _ (Mu-el _ (Id ob1 × hom12) ~ hom12)
    :runit-fw =
      (2ob @(ob1 ~ ob2) : [2~] Ob) (hom12 : Hom.El (ob1 > ob2)) →
      Hom.To _ (hom12 ~ Mu-el _ (hom12 × Id ob2))
    :runit-bw =
      (2ob @(ob1 ~ ob2) : [2~] Ob) (hom12 : Hom.El (ob1 > ob2)) →
      Hom.To _ (Mu-el _ (hom12 × Id ob2) ~ hom12)
    :bunit-fw =
      (ob : Ob) →
      Hom.To _ (Id ob ~ Mu-el _ (Id ob × Id ob))
    :bunit-bw =
      (ob : Ob) →
      Hom.To _ (Mu-el _ (Id ob × Id ob) ~ Id ob)

  module _ (oper : [Obj-oper]) where
    record [Obj-prop] : [Any] where
      constructor ‼
      open :[Obj-prop] oper

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

  -- data:
  field Hom : :Hom Ob
  field oper : [Obj-oper] Ob Hom
  field prop : [Obj-prop] Ob Hom oper

  -- helpers:
  private module Hom (2ob : [2~] Ob) = Set.[Ob] (Hom 2ob)
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

Hom-Opp-Hom = Set-Qu.Hom-Opp-Hom
To-Opp-Hom  = Set-Qu.To-Opp-Hom

module _ (Ob : [Any]) (Hom : :Hom Ob) where
  open [Obj-oper]

  Hom-Opp-oper : [Obj-oper] Ob Hom → [Obj-oper] Ob (Hom-Opp-Hom _ Hom)
  Hom-Opp-oper oper .Id _ = oper .Id _
  Hom-Opp-oper oper .Mu _ .↓ .f-el (h12 × h23) = oper .Mu _ .f-el (h23 × h12)
  Hom-Opp-oper oper .Mu _ .↓ .f-to _ (hto12 × hto23) = oper .Mu _ .f-to _ (hto23 × hto12)

  To-Opp-oper : [Obj-oper] Ob Hom → [Obj-oper] Ob (To-Opp-Hom _ Hom)
  To-Opp-oper oper .Id _ = oper .Id _
  To-Opp-oper oper .Mu _ .↓ .f-el = oper .Mu _ .f-el
  To-Opp-oper oper .Mu _ .↓ .f-to _ = oper .Mu _ .f-to _

module _ (Ob : [Any]) (Hom : :Hom Ob) (oper : [Obj-oper] Ob Hom) where
  open [Obj-prop]

  Hom-Opp-prop : [Obj-prop] _ _ oper → [Obj-prop] _ _ (Hom-Opp-oper _ _ oper)
  Hom-Opp-prop prop .assoc-fw _ (h12 × h23 × h34) = prop .assoc-bw _ (h34 × h23 × h12)
  Hom-Opp-prop prop .assoc-bw _ (h12 × h23 × h34) = prop .assoc-fw _ (h34 × h23 × h12)
  Hom-Opp-prop prop .lunit-fw _ h12 = prop .runit-fw _ h12
  Hom-Opp-prop prop .lunit-bw _ h12 = prop .runit-bw _ h12
  Hom-Opp-prop prop .runit-fw _ h12 = prop .lunit-fw _ h12
  Hom-Opp-prop prop .runit-bw _ h12 = prop .lunit-bw _ h12
  Hom-Opp-prop prop .bunit-fw _ = prop .bunit-fw _
  Hom-Opp-prop prop .bunit-bw _ = prop .bunit-bw _

  To-Opp-prop : [Obj-prop] _ _ oper → [Obj-prop] _ _ (To-Opp-oper _ _ oper)
  To-Opp-prop prop .assoc-fw = prop .assoc-bw
  To-Opp-prop prop .assoc-bw = prop .assoc-fw
  To-Opp-prop prop .lunit-fw = prop .lunit-bw
  To-Opp-prop prop .lunit-bw = prop .lunit-fw
  To-Opp-prop prop .runit-fw = prop .runit-bw
  To-Opp-prop prop .runit-bw = prop .runit-fw
  To-Opp-prop prop .bunit-fw = prop .bunit-bw
  To-Opp-prop prop .bunit-bw = prop .bunit-fw

module _ (Ob : [Any]) where
  open [is-Obj]

  Hom-Opp-is : [is-Obj] Ob → [is-Obj] Ob
  Hom-Opp-is is .Hom  = Hom-Opp-Hom  _ (is .Hom)
  Hom-Opp-is is .oper = Hom-Opp-oper _ _ (is .oper)
  Hom-Opp-is is .prop = Hom-Opp-prop _ _ _ (is .prop)

  To-Opp-is : [is-Obj] Ob → [is-Obj] Ob
  To-Opp-is is .Hom  = To-Opp-Hom  _ (is .Hom)
  To-Opp-is is .oper = To-Opp-oper _ _ (is .oper)
  To-Opp-is is .prop = To-Opp-prop _ _ _ (is .prop)
