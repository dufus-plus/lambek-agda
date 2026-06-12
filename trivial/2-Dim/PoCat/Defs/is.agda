open import 0-Dim
import 1-Dim.AnyPoSet.Defs as AnyPoSet
import 1-Dim.PoSet.Def-Types as PoSet
open import 1-Dim.PoSet.Def-Types-pub.Ob
open import 1-Dim.PoSet.Def-Types-pub.Fun
import 2-Dim.PoSet-Graph.Defs.Ob as PoSet-Graph

module 2-Dim.PoCat.Defs.is where

open PoSet-Graph using (‼)

module _ (Graph @(‼ $Ob Hom) : PoSet-Graph.[Ob]) where
  module :oper  where
    -- operations on Hom: (id)entity, (mu)ltiplication
    :Id = AnyPoSet.Rel-[0Fun] _ (! > Hom)
    :Mu = AnyPoSet.Rel-[2Fun] _ ((Hom × Hom) > Hom)

  record [oper] : [Any] where
    constructor ‼
    open :oper
    field Id : :Id
    field Mu : :Mu
  open [oper]

  module :prop (oper @(‼ Id Mu): [oper]) where
    -- associativity of multiplication
    :Assoc-fw =
      (4ob @(ob1 ~ ob2 ~ ob3 ~ ob4) : [4~] $Ob)
      (3hom @(hom12 × hom23 × hom34):
        Hom (ob1 > ob2) .Ob [×] Hom (ob2 > ob3) .Ob [×] Hom (ob3 > ob4) .Ob) →
      Hom _ .To ((Mu _ .f-ob (Mu _ .f-ob (hom12 × hom23) × hom34)) ~
                  (Mu _ .f-ob (hom12 × Mu _ .f-ob (hom23 × hom34))))
    :Assoc-bw =
      (4ob @(ob1 ~ ob2 ~ ob3 ~ ob4) : [4~] $Ob)
      (3hom @(hom12 × hom23 × hom34):
        Hom (ob1 > ob2) .Ob [×] Hom (ob2 > ob3) .Ob [×] Hom (ob3 > ob4) .Ob) →
      Hom _ .To ((Mu _ .f-ob (hom12 × Mu _ .f-ob (hom23 × hom34))) ~
                  (Mu _ .f-ob (Mu _ .f-ob (hom12 × hom23) × hom34)))
    -- identity is (left,right) unit
    :LUnit-fw =
      (2ob @(ob1 ~ ob2) : [2~] $Ob) (hom12 : Hom (ob1 > ob2) .Ob) →
      Hom _ .To (hom12 ~ Mu _ .f-ob (Id ob1 × hom12))
    :LUnit-bw =
      (2ob @(ob1 ~ ob2) : [2~] $Ob) (hom12 : Hom (ob1 > ob2) .Ob) →
      Hom _ .To (Mu _ .f-ob (Id ob1 × hom12) ~ hom12)
    :RUnit-fw =
      (2ob @(ob1 ~ ob2) : [2~] $Ob) (hom12 : Hom (ob1 > ob2) .Ob) →
      Hom _ .To (hom12 ~ Mu _ .f-ob (hom12 × Id ob2))
    :RUnit-bw =
      (2ob @(ob1 ~ ob2) : [2~] $Ob) (hom12 : Hom (ob1 > ob2) .Ob) →
      Hom _ .To (Mu _ .f-ob (hom12 × Id ob2) ~ hom12)
    :BUnit-fw =
      (ob : $Ob) →
      Hom _ .To (Id ob ~ Mu _ .f-ob (Id ob × Id ob))
    :BUnit-bw =
      (ob : $Ob) →
      Hom _ .To (Mu _ .f-ob (Id ob × Id ob) ~ Id ob)

module _ (Graph : PoSet-Graph.[Ob]) (oper : [oper] Graph) where
  record [prop] : [Any] where
    constructor ‼
    open :prop Graph oper
    field Assoc-fw : :Assoc-fw
    field Assoc-bw : :Assoc-bw
    field LUnit-fw : :LUnit-fw
    field LUnit-bw : :LUnit-bw
    field RUnit-fw : :RUnit-fw
    field RUnit-bw : :RUnit-bw
    field BUnit-fw : :BUnit-fw
    field BUnit-bw : :BUnit-bw
