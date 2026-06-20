open import 0-Dim.!quali
import 1-Dim.Set.Def-Types as Set
import 2-Dim-Pre.Set-Qu.Def-Types.Fun as Set-Qu
open import 2-Dim.Cat.Def-Types.Obj

module 2-Dim.Cat.Def-Types.Fun where

module _ (AB @(A > B) : [2~] [Obj]) where
  open [Obj]
  open Set.[Ob]
  open Set.[Fun]
  open Set-Qu using (‼)

  module :is-Fun (It @(‼ F-Ob F-Hom) : Quiver.[Fun] (A .It > B .It)) where
    :F-Id-fw = (a : A .Ob) →
      B .Hom _ .To (F-Hom _ .f-el (A .Id a) ~ B .Id (F-Ob a))
    :F-Id-bw = (a : A .Ob) →
      B .Hom _ .To (B .Id (F-Ob a) ~ F-Hom _ .f-el (A .Id a))
    :F-Mu-fw = (3a @(a1 ~ a2 ~ a3) : [3~] A .Ob) →
               (2hom @(a12 × a23) : A .Hom (a1 ~ a2) .El [×] A .Hom (a2 ~ a3) .El) →
      B .Hom _ .To (F-Hom _ .f-el (A .Mu _ .f-el 2hom) ~
                    B .Mu _ .f-el (F-Hom _ .f-el a12 × F-Hom _ .f-el a23))
    :F-Mu-bw = (3a @(a1 ~ a2 ~ a3) : [3~] A .Ob) →
               (2hom @(a12 × a23) : A .Hom (a1 ~ a2) .El [×] A .Hom (a2 ~ a3) .El) →
      B .Hom _ .To (B .Mu _ .f-el (F-Hom _ .f-el a12 × F-Hom _ .f-el a23) ~
                    F-Hom _ .f-el (A .Mu _ .f-el 2hom))

  record [is-Fun] (↓ : Quiver.[Fun] (A .It > B .It)) : [Any] where
    constructor ‼
    open :is-Fun ↓
    field F-Id-fw : :F-Id-fw
    field F-Id-bw : :F-Id-bw
    field F-Mu-fw : :F-Mu-fw
    field F-Mu-bw : :F-Mu-bw

module _ (AB @(A > B) : [2~] [Obj]) where
  module :[Fun] where
    open [Obj]
    :It = Quiver.[Fun] (A .It > B .It)
    module _ (It : :It) where
      :is = [is-Fun] AB It

  record [Fun] : [Any] where
    constructor ‼
    open :[Fun]

    field It : :It
    open Quiver.[Fun] It public

    field is : [is-Fun] AB It
    open [is-Fun] is public
