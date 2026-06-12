open import 0-Dim
import 1-Dim.AnySet.Defs as AnySet
import 1-Dim.Set.Defs as Set
import 2-Dim.Set-Graph.Defs.Ob as Set-Graph

module 2-Dim.Cat.Defs.is where

open Set-Graph using (‼)
open Set.[Ob]
open Set.[Fun]

module _ (Graph @(‼ $Ob Hom) : Set-Graph.[Ob]) where
  module :oper  where
    -- operations on Hom: (id)entity, (mu)ltiplication
    :Id = AnySet.Rel-[0Fun] _ (! > Hom)
    :Mu = AnySet.Rel-[2Fun] _ ((Hom × Hom) > Hom)

  record [oper] : [Any] where
    constructor ‼
    open :oper
    field Id : :Id
    field Mu : :Mu
  open [oper]

  module _ (oper @(‼ Id Mu): [oper]) where
    module :prop  where
      -- associativity of multiplication
      :Mu-Assoc-fw =
        (4ob @(ob1 ~ ob2 ~ ob3 ~ ob4) : [4~] $Ob)
        (3hom @(hom12 × hom23 × hom34):
          Hom (ob1 > ob2) .Ob [×] Hom (ob2 > ob3) .Ob [×] Hom (ob3 > ob4) .Ob) →
        Hom _ .To ((Mu _ .f-ob (Mu _ .f-ob (hom12 × hom23) × hom34)) ~
                    (Mu _ .f-ob (hom12 × Mu _ .f-ob (hom23 × hom34))))
      :Mu-Assoc-bw =
        (4ob @(ob1 ~ ob2 ~ ob3 ~ ob4) : [4~] $Ob)
        (3hom @(hom12 × hom23 × hom34):
          Hom (ob1 > ob2) .Ob [×] Hom (ob2 > ob3) .Ob [×] Hom (ob3 > ob4) .Ob) →
        Hom _ .To ((Mu _ .f-ob (hom12 × Mu _ .f-ob (hom23 × hom34))) ~
                    (Mu _ .f-ob (Mu _ .f-ob (hom12 × hom23) × hom34)))

      -- identity is (left,right) unit
      :Id-LUnit-fw =
        (2ob @(ob1 ~ ob2) : [2~] $Ob) (hom12 : Hom (ob1 > ob2) .Ob) →
        Hom _ .To (hom12 ~ Mu _ .f-ob (Id ob1 × hom12))
      :Id-LUnit-bw =
        (2ob @(ob1 ~ ob2) : [2~] $Ob) (hom12 : Hom (ob1 > ob2) .Ob) →
        Hom _ .To (Mu _ .f-ob (Id ob1 × hom12) ~ hom12)
      :Id-RUnit-fw =
        (2ob @(ob1 ~ ob2) : [2~] $Ob) (hom12 : Hom (ob1 > ob2) .Ob) →
        Hom _ .To (hom12 ~ Mu _ .f-ob (hom12 × Id ob2))
      :Id-RUnit-bw =
        (2ob @(ob1 ~ ob2) : [2~] $Ob) (hom12 : Hom (ob1 > ob2) .Ob) →
        Hom _ .To (Mu _ .f-ob (hom12 × Id ob2) ~ hom12)

module _ (Graph : Set-Graph.[Ob]) (oper : [oper] Graph) where
  record [prop] : [Any] where
    constructor ‼
    open :prop Graph oper
    field Mu-Assoc-fw : :Mu-Assoc-fw
    field Mu-Assoc-bw : :Mu-Assoc-bw
    field Id-LUnit-fw : :Id-LUnit-fw
    field Id-LUnit-bw : :Id-LUnit-bw
    field Id-RUnit-fw : :Id-RUnit-fw
    field Id-RUnit-bw : :Id-RUnit-bw
  open [prop]
