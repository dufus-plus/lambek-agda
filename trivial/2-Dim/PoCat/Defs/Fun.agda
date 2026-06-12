open import 0-Dim
import 1-Dim.PoSet.Defs as PoSet
open import 2-Dim.PoCat.Defs.Ob
import 2-Dim.PoSet-Graph.Defs.Fun as PoSet-Graph

module 2-Dim.PoCat.Defs.Fun where

module _ (AB @(A > B) : [2~] [Ob]) where
  open [Ob]
  open PoSet.[Ob]
  open PoSet.[Fun]
  open PoSet-Graph using (‼)

  module :is-Fun (It @(‼ F-Ob F-Hom) : PoSet-Graph.[Fun] (A .↓ > B .↓)) where
    :F-Id-fw = (a : A .Ob) →
      B .Hom _ .To (F-Hom _ .f-ob (A .Id a) ~ B .Id (F-Ob a))
    :F-Id-bw = (a : A .Ob) →
      B .Hom _ .To (B .Id (F-Ob a) ~ F-Hom _ .f-ob (A .Id a))
    :F-Mu-fw = (3a @(a1 ~ a2 ~ a3) : [3~] A .Ob) →
               (2hom @(a12 × a23) : A .Hom (a1 ~ a2) .Ob [×] A .Hom (a2 ~ a3) .Ob) →
      B .Hom _ .To (F-Hom _ .f-ob (A .Mu _ .f-ob 2hom) ~
                    B .Mu _ .f-ob (F-Hom _ .f-ob a12 × F-Hom _ .f-ob a23))
    :F-Mu-bw = (3a @(a1 ~ a2 ~ a3) : [3~] A .Ob) →
               (2hom @(a12 × a23) : A .Hom (a1 ~ a2) .Ob [×] A .Hom (a2 ~ a3) .Ob) →
      B .Hom _ .To (B .Mu _ .f-ob (F-Hom _ .f-ob a12 × F-Hom _ .f-ob a23) ~
                    F-Hom _ .f-ob (A .Mu _ .f-ob 2hom))

  record [is-Fun] (↓ : PoSet-Graph.[Fun] (A .↓ > B .↓)) : [Any] where
    constructor ‼
    open :is-Fun ↓
    field F-Id-fw : :F-Id-fw
    field F-Id-bw : :F-Id-bw
    field F-Mu-fw : :F-Mu-fw
    field F-Mu-bw : :F-Mu-bw

module _ (AB @(A > B) : [2~] [Ob]) where
  module :Fun where
    open [Ob]
    :It = PoSet-Graph.[Fun] (A .↓ > B .↓)
    module _ (It : :It) where
      :is = [is-Fun] AB It

  record [Fun] : [Any] where
    constructor ‼
    open :Fun
    field ↓ : :It
    open PoSet-Graph.[Fun] ↓ public
    field is : [is-Fun] AB ↓
    open [is-Fun] is public
