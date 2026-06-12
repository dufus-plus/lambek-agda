open import 0-Dim
open import 2-Dim.PoCat.Defs.Ob
open import 2-Dim.PoCat.Defs.Fun
open import 2-Dim.PoCat.Defs.Fun-Hom
open import 2-Dim.PoCat.Defs.Hom

module 2-Dim.PoCat.Defs.Fun-Hom-To where

module _ (2C @(A ~ B) : [2~] [Ob])
         (2F @(F1 ~ F2) : [2~] [Fun] 2C)
         (2h @(hom1 ~ hom2) : [2~] Fun-[Hom] 2C 2F) where
  open [Ob]
  open Fun-[Hom]

  :Fun-Hom-To = (a : A .Ob) → Hom-[To] B _ (hom1 .n-ob a ~ hom2 .n-ob a)

  record Fun-Hom-[To] : [Any] where
    constructor ↑
    field ↓ : :Fun-Hom-To
