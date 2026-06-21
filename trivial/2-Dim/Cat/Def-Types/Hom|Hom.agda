open import 0-Dim.!quali
open import 2-Dim.Cat.Def-Types.Obj
open import 2-Dim.Cat.Def-Types-pub.Obj

module 2-Dim.Cat.Def-Types.Hom|Hom (C : [Obj]) where

[Dup|Hom] = Any.[Dup|R] (2~ C .Hom-El)
[Hom|Dup] = Any.[R|Dup] (2~ C .Hom-El)

module _ (22ob : [22~] C. Ob)
         (2VF @(VF1 > VF2) : [Dup|Hom] 22ob)
         (2HF @(HF1 ~ HF2) : [Hom|Dup] 22ob) where

  :Hom|Hom : [Any]
  :Hom|Hom = C .Hom-To _ (C .Mu-el _ (VF1 × HF2) ~ C .Mu-el _ (HF1 × VF2))

  record [Hom|Hom] : [Any] where
    constructor ↑
    field ↓ : :Hom|Hom
