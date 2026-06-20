open import 0-Dim.!quali
import 2-Dim-Pre.Matr.Def-Types as AnySet
import 1-Dim.Set.Def-Types as Set
open import 1-Dim.Set.Def-Types-pub
import 2-Dim-Pre.Set-Qu.Def-Types.Obj as Set-Qu

module 2-Dim.Cat.Def-Types.is-Obj where

open Set-Qu using (‼)

module _ (Quiver @(‼ $Ob Hom) : Quiver.[Obj]) where
  module :[oper]  where
    -- operations on Hom: (id)entity, (mu)ltiplication
    :Id = AnySet.Rel-[0-Fun] _ (! > Hom)
    :Mu = AnySet.Rel-[2-Fun] _ ((Hom × Hom) > Hom)

  record [oper] : [Any] where
    constructor ‼
    open :[oper]
    field Id : :Id
    field Mu : :Mu
  open [oper]

  module :[prop] (oper @(‼ Id Mu): [oper]) where
    -- associativity of multiplication
    :Assoc-fw =
      (4ob @(ob1 ~ ob2 ~ ob3 ~ ob4) : [4~] $Ob)
      (3hom @(hom12 × hom23 × hom34):
        Hom (ob1 > ob2) .El [×] Hom (ob2 > ob3) .El [×] Hom (ob3 > ob4) .El) →
      Hom _ .To ((Mu _ .f-el (Mu _ .f-el (hom12 × hom23) × hom34)) ~
                  (Mu _ .f-el (hom12 × Mu _ .f-el (hom23 × hom34))))
    :Assoc-bw =
      (4ob @(ob1 ~ ob2 ~ ob3 ~ ob4) : [4~] $Ob)
      (3hom @(hom12 × hom23 × hom34):
        Hom (ob1 > ob2) .El [×] Hom (ob2 > ob3) .El [×] Hom (ob3 > ob4) .El) →
      Hom _ .To ((Mu _ .f-el (hom12 × Mu _ .f-el (hom23 × hom34))) ~
                  (Mu _ .f-el (Mu _ .f-el (hom12 × hom23) × hom34)))
    -- identity is (left,right) unit
    :LUnit-fw =
      (2ob @(ob1 ~ ob2) : [2~] $Ob) (hom12 : Hom (ob1 > ob2) .El) →
      Hom _ .To (hom12 ~ Mu _ .f-el (Id ob1 × hom12))
    :LUnit-bw =
      (2ob @(ob1 ~ ob2) : [2~] $Ob) (hom12 : Hom (ob1 > ob2) .El) →
      Hom _ .To (Mu _ .f-el (Id ob1 × hom12) ~ hom12)
    :RUnit-fw =
      (2ob @(ob1 ~ ob2) : [2~] $Ob) (hom12 : Hom (ob1 > ob2) .El) →
      Hom _ .To (hom12 ~ Mu _ .f-el (hom12 × Id ob2))
    :RUnit-bw =
      (2ob @(ob1 ~ ob2) : [2~] $Ob) (hom12 : Hom (ob1 > ob2) .El) →
      Hom _ .To (Mu _ .f-el (hom12 × Id ob2) ~ hom12)
    :BUnit-fw =
      (ob : $Ob) →
      Hom _ .To (Id ob ~ Mu _ .f-el (Id ob × Id ob))
    :BUnit-bw =
      (ob : $Ob) →
      Hom _ .To (Mu _ .f-el (Id ob × Id ob) ~ Id ob)

module _ (Quiver : Quiver.[Obj]) (oper : [oper] Quiver) where
  record [prop] : [Any] where
    constructor ‼
    open :[prop] Quiver oper
    field Assoc-fw : :Assoc-fw
    field Assoc-bw : :Assoc-bw
    field LUnit-fw : :LUnit-fw
    field LUnit-bw : :LUnit-bw
    field RUnit-fw : :RUnit-fw
    field RUnit-bw : :RUnit-bw
    field BUnit-fw : :BUnit-fw
    field BUnit-bw : :BUnit-bw
