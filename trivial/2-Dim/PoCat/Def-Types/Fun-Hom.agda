open import 0-Dim.!quali
import 1-Dim.PoSet.Def-Types as PoSet
open import 1-Dim.PoSet.Def-Types-pub
open import 2-Dim.PoCat.Def-Types.Obj
open import 2-Dim.PoCat.Def-Types-pub.Obj
open import 2-Dim.PoCat.Def-Types.Fun
open import 2-Dim.PoCat.Def-Types-pub.Fun
open import 2-Dim.PoCat.Def-Types.Hom
open import 2-Dim.PoCat.Def-Types.Hom|Hom

module 2-Dim.PoCat.Def-Types.Fun-Hom where

module _ (2C @(A ~ B) : [2~] [Obj])
         (2F @(F ~ G) : [2~] [Fun] 2C) where
  module :Fun-Hom where

    :n-ob = (a : A .Ob) → [Hom] B (F .f-el a > G .f-el a)
    module _ (n-ob : :n-ob) where
      :n-hom-fw = (2a @(a1 ~ a2) : [2~] A .Ob) → (hom : [Hom] A 2a) →
        [Hom|Hom] B _
          (n-ob a1 ~ n-ob a2)
          (F .F-Hom _ .f-el hom ~ G .F-Hom _ .f-el hom)
      :n-hom-bw = (2a @(a1 ~ a2) : [2~] A .Ob) → (hom : [Hom] A 2a) →
        [Hom|Hom] B _
          (F .F-Hom _ .f-el hom ~ G .F-Hom _ .f-el hom)
          (n-ob a1 ~ n-ob a2)

  record Fun-[Hom] : [Any] where
    constructor ‼
    open :Fun-Hom
    field n-ob : :n-ob
    field n-hom-fw : :n-hom-fw n-ob
    field n-hom-bw : :n-hom-bw n-ob
