open import 0-Dim.!quali
open import 2-Dim.Cat.Def-Types.Obj
open import 2-Dim.Cat.Def-Types.Fun
open import 2-Dim.Cat.Def-Types.Fun-Hom
open import 2-Dim.Cat.Def-Types-pub.Obj
open import 2-Dim.Cat.Def-Types-pub.Fun
open import 2-Dim.Cat.Def-Types-pub.Fun-Hom
open import 2-Dim.Cat.Def-Types.Hom

--
-- natural transformation between functors
--
module 2-Dim.Cat.Def-Types.Fun-Hom-To where

module _ (2C @(A ~ B) : [2~] [Obj])
         (2F @(F1 ~ F2) : [2~] [Fun] 2C)
         (2h @(hom1 ~ hom2) : [2~] Fun-[Hom] 2C 2F) where

  :Fun-Hom-To : [Any]
  :Fun-Hom-To = (a : A .Ob) → Hom-[To] B _ (hom1 .n-ob a ~ hom2 .n-ob a)

  record Fun-Hom-[To] : [Any] where
    constructor ↑
    field ↓ : :Fun-Hom-To
