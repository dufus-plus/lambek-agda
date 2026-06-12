open import 0-Dim
import 1-Dim.PoSet.Defs as PoSet
open import 2-Dim.PoCat.Defs.Ob
open import 2-Dim.PoCat.Defs.Hom

module 2-Dim.PoCat.Defs.Hom|Hom where

open [Ob]
open PoSet.[Ob]
open PoSet.[Fun]

module _ (C : [Ob])
         (22ob : [22~] C. Ob)
         (2VF @(VF1 > VF2) : [Dup|Hom] C 22ob)
         (2HF @(HF1 ~ HF2) : [Hom|Dup] C 22ob) where

  :Hom|Hom : [Any]
  :Hom|Hom = Hom-[To] C _ (Hom-Mu C _ (VF1 × HF2) ~ Hom-Mu C _ (HF1 × VF2))

  record [Hom|Hom] : [Any] where
    constructor ↑
    field ↓ : :Hom|Hom
