open import 0-Dim
import 1-Dim.PoSet.Defs as PoSet
open import 2-Dim.PoCat.Defs.Ob
open import 2-Dim.PoCat.Defs.Hom
open import 2-Dim.PoCat.Defs.Hom|Hom
open import 2-Dim.PoCat.Defs.Fun

module 2-Dim.PoCat.Defs.Fun-Hom where

module _ (2C @(A ~ B) : [2~] [Ob])
         (2F @(F ~ G) : [2~] [Fun] 2C) where
  module :Fun-Hom where
    open [Ob]
    open [Fun]
    open PoSet.[Ob]
    open PoSet.[Fun]

    :n-ob = (a : A .Ob) → [Hom] B (F .F-Ob a > G .F-Ob a)
    module _ (n-ob : :n-ob) where
      :n-hom-fw = (2a @(a1 ~ a2) : [2~] A .Ob) → (hom : [Hom] A 2a) →
        [Hom|Hom] B _
          (n-ob a1 ~ n-ob a2)
          (F .F-Hom _ .f-ob hom ~ G .F-Hom _ .f-ob hom)
      :n-hom-bw = (2a @(a1 ~ a2) : [2~] A .Ob) → (hom : [Hom] A 2a) →
        [Hom|Hom] B _
          (F .F-Hom _ .f-ob hom ~ G .F-Hom _ .f-ob hom)
          (n-ob a1 ~ n-ob a2)

  record Fun-[Hom] : [Any] where
    constructor ‼
    open :Fun-Hom
    field n-ob : :n-ob
    field n-hom-fw : :n-hom-fw n-ob
    field n-hom-bw : :n-hom-bw n-ob
