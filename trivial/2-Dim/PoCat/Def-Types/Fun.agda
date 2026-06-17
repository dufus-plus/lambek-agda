open import 0-Dim.!quali
import 1-Dim.PoSet.Def-Types as PoSet
import 2-Dim.PoQuiver.Def-Types.Fun as PoQuiver
open import 2-Dim.PoCat.Def-Types.Obj

module 2-Dim.PoCat.Def-Types.Fun where

module _ (AB @(A > B) : [2~] [Obj]) where
  open [Obj]
  open PoSet.[Ob]
  open PoSet.[Fun]
  open PoQuiver using (‼)

  module :is-Fun (It @(‼ F-Ob F-Hom) : PoQuiver.[Fun] (A .It > B .It)) where
    :F-Id-fw = (a : A .Ob) →
      B .Hom _ .To (F-Hom _ .f-ob (A .Id a) ~ B .Id (F-Ob a))
    :F-Id-bw = (a : A .Ob) →
      B .Hom _ .To (B .Id (F-Ob a) ~ F-Hom _ .f-ob (A .Id a))
    :F-Mu-fw = (3a @(a1 ~ a2 ~ a3) : [3~] A .Ob) →
               (2hom @(a12 × a23) : A .Hom (a1 ~ a2) .El [×] A .Hom (a2 ~ a3) .El) →
      B .Hom _ .To (F-Hom _ .f-ob (A .Mu _ .f-ob 2hom) ~
                    B .Mu _ .f-ob (F-Hom _ .f-ob a12 × F-Hom _ .f-ob a23))
    :F-Mu-bw = (3a @(a1 ~ a2 ~ a3) : [3~] A .Ob) →
               (2hom @(a12 × a23) : A .Hom (a1 ~ a2) .El [×] A .Hom (a2 ~ a3) .El) →
      B .Hom _ .To (B .Mu _ .f-ob (F-Hom _ .f-ob a12 × F-Hom _ .f-ob a23) ~
                    F-Hom _ .f-ob (A .Mu _ .f-ob 2hom))

  record [is-Fun] (↓ : PoQuiver.[Fun] (A .It > B .It)) : [Any] where
    constructor ‼
    open :is-Fun ↓
    field F-Id-fw : :F-Id-fw
    field F-Id-bw : :F-Id-bw
    field F-Mu-fw : :F-Mu-fw
    field F-Mu-bw : :F-Mu-bw

module _ (AB @(A > B) : [2~] [Obj]) where
  module :[Fun] where
    open [Obj]
    :It = PoQuiver.[Fun] (A .It > B .It)
    module _ (It : :It) where
      :is = [is-Fun] AB It

  record [Fun] : [Any] where
    constructor ‼
    open :[Fun]

    field It : :It
    open PoQuiver.[Fun] It public

    field is : [is-Fun] AB It
    open [is-Fun] is public
