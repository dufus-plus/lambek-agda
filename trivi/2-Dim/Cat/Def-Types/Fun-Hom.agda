open import 0-Dim.!quali
open import 1-Dim.Set.Def-Types-pub
open import 2-Dim.Cat.Def-Types.Obj
open import 2-Dim.Cat.Def-Types-pub.Obj
open import 2-Dim.Cat.Def-Types.Fun
open import 2-Dim.Cat.Def-Types-pub.Fun
open import 2-Dim.Cat.Def-Types.Hom|Hom

module 2-Dim.Cat.Def-Types.Fun-Hom where

module _ (2C @(A ~ B) : [2~] [Obj])
         (2F @(F ~ G) : [2~] [Fun] 2C) where
  module :Fun-Hom where
    :n-ob = (a : A .Ob) → B .Hom-El (F .f-ob a > G .f-ob a)

    module _ (n-ob : :n-ob) where
      :n-hom-fw =
        (2a @(a1 ~ a2) : [2~] A .Ob) →
        (hom : A .Hom-El 2a) →
        [Hom|Hom] B _
          (n-ob a1 ~ n-ob a2)
          (F .f-hom-el _ hom ~ G .f-hom-el _ hom)
      :n-hom-bw =
        (2a @(a1 ~ a2) : [2~] A .Ob) →
        (hom : A .Hom-El 2a) →
        [Hom|Hom] B _
          (F .f-hom-el _ hom ~ G .f-hom-el _ hom)
          (n-ob a1 ~ n-ob a2)

  record Fun-[Hom] : Any where
    constructor ‼
    open :Fun-Hom

    -- data:
    field n-ob : :n-ob
    field n-hom-fw : :n-hom-fw n-ob
    field n-hom-bw : :n-hom-bw n-ob
