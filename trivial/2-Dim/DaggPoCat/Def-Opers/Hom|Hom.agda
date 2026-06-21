open import 0-Dim.!quali
open import 1-Dim.PoSet.!publi
open import 2-Dim.DaggPoCat.Def-Types
open import 2-Dim.DaggPoCat.Def-Types-pub
import 2-Dim-Pre.Matr.Def-Types as Matr
open import 2-Dim-Pre.Matr.Def-Types-pub
import 2-Dim.PoCat|PoCat.Def-Types.is-Obj as PoCat|PoCat
open import 2-Dim.PoCat|PoCat.Def-Types-pub.is-Obj

module 2-Dim.DaggPoCat.Def-Opers.Hom|Hom where

module _
    (C : [Obj]) (let module C = [Obj] C)
    (let C' = To-Opp C) (let module C' = [Obj] C')
  where

  module Hom|Hom where
    -- C.Hom-To _ (C.Mu-el _ (VF1 × HF2) ~ C.Mu-el _ (HF1 × VF2))
    R|R : Matr.[PoSet|PoSet] _ (2~ C.Hom) (2~ C'.Hom)
    R|R .Sqr = [Hom|Hom] C

    R|R .H-lact _ _ (h1 ~ h2) (vto1 × h|v2) .↓ =
      C.Hom-tran _ _ (C.Mu-to _ _ (vto1 × C.Hom-refl _ h2) × h|v2 .↓)
    R|R .H-ract _ _ (h1 ~ h2) (h|v1 × vto2) .↓ =
      C.Hom-tran _ _ (h|v1 .↓ × C.Mu-to _ _ (C.Hom-refl _ h1 × vto2))
    R|R .V-lact _ (v1 ~ v2) _ (hto1 × h|v2) .↓ =
      C.Hom-tran _ _ (h|v2 .↓ × C.Mu-to _ _ (hto1 × C.Hom-refl _ v2))
    R|R .V-ract _ (v1 ~ v2) _ (h|v1 × hto2) .↓ =
      C.Hom-tran _ _ (C.Mu-to _ _ (C.Hom-refl _ v1 × hto2) × h|v1 .↓)

  open PoCat|PoCat.:[is-Obj] C.Ob C'.is-PoCat C.is-PoCat Hom|Hom.R|R

  Hom-Id|Hom : :H-Id|V
  Hom|Hom-Id : :H|V-Id
  Hom-Mu|Hom : :H-Mu|V
  Hom|Hom-Mu : :H|V-Mu

  Hom-Id|Hom _ V .↓ = C.Hom-tran _ _ (C.runit-bw _ V × C.lunit-fw _ V)
  Hom|Hom-Id _ H .↓ = C.Hom-tran _ _ (C.lunit-bw _ H × C.runit-fw _ H)

  Hom-Mu|Hom _ (V1 ~ V2 ~ V3) ((H11 × H12) ~ (H21 × H22)) (hv1 × hv2) .↓ =
    C.Hom _ .tran _
    ( C.assoc-bw _ (V1 × H21 × H22) ×
      C.Hom _ .tran _
      ( (C.Mu _ .f-to _ (hv1 .↓ × C.Hom _ .refl H22)) ×
        C.Hom _ .tran _
        ( (C.assoc-fw _ (H11 × V2 × H22)) ×
          C.Hom _ .tran _
          ( C.Mu _ .f-to _ (C.Hom _ .refl H11 × hv2 .↓) ×
            C.assoc-bw _ (H11 × H12 × V3) ) ) ) )

  Hom|Hom-Mu _ ((V11 × V21) ~ (V12 × V22)) (H1 ~ H2 ~ H3) (hv1 × hv2) .↓ =
    C.Hom _ .tran _
    ( C.assoc-fw _ (V11 × V21 × H3) ×
      C.Hom _ .tran _
      ( (C.Mu _ .f-to _ (C.Hom _ .refl V11 × hv2 .↓)) ×
        C.Hom _ .tran _
        ( (C.assoc-bw _ (V11 × H2 × V22)) ×
          C.Hom _ .tran _
          ( C.Mu _ .f-to _ (hv1 .↓ × C.Hom _ .refl V22) ×
            C.assoc-fw _ (H1 × V12 × V22) ) ) ) )

  I→Hom|Hom : :I→H|V
  Hom→I|Hom : :H→I|V
  Hom|I→Hom : :H|I→V
  Hom|Hom→I : :H|V→I

  I→Hom|Hom _ (v1 ~ v2) vto = Hom|Hom.R|R .H-lact _ _ _ (vto × Hom-Id|Hom _ v2)

  Hom→I|Hom _ (v1 ~ v2) hv =
    C.Hom-tran _ _
    ( C.runit-fw _ v1 ×
      C.Hom-tran _ _
      ( hv .↓ ×
        C.lunit-bw _ v2 ) )

  Hom|I→Hom _ (h1 ~ h2) hto = Hom|Hom.R|R .V-lact _ _ _ (hto × Hom|Hom-Id _ h2)

  Hom|Hom→I _ (h1 ~ h2) hv =
    C.Hom-tran _ _
    ( C.lunit-fw _ h2 ×
      C.Hom-tran _ _
      ( hv .↓ ×
        C.runit-bw _ h1 ) )

  Hom|Hom-is-PC|PC : PoCat|PoCat.[is-Obj] C.Ob C'.is-PoCat C.is-PoCat Hom|Hom.R|R

  Hom|Hom-is-PC|PC .H-Id|V = Hom-Id|Hom
  Hom|Hom-is-PC|PC .H|V-Id = Hom|Hom-Id
  Hom|Hom-is-PC|PC .H-Mu|V = Hom-Mu|Hom
  Hom|Hom-is-PC|PC .H|V-Mu = Hom|Hom-Mu

  Hom|Hom-is-PC|PC .I→H|V = I→Hom|Hom
  Hom|Hom-is-PC|PC .H→I|V = Hom→I|Hom
  Hom|Hom-is-PC|PC .H|I→V = Hom|I→Hom
  Hom|Hom-is-PC|PC .H|V→I = Hom|Hom→I

Fun-Hom|Hom :
  (2C@(A ~ B) : [2~] [Obj])
  (F : [Fun] 2C) →
  (22ob : [22~] A. Ob)
  (2VF @(VF1 > VF2) : [Dup|Hom] A 22ob)
  (2HF @(HF1 ~ HF2) : [Hom|Dup] A 22ob)
  (HH : [Hom|Hom] A _ 2VF 2HF) →
  [Hom|Hom] B _ (F .f-hom-el _ VF1 ~ F .f-hom-el _ VF2)
                (F .f-hom-el _ HF1 ~ F .f-hom-el _ HF2)
Fun-Hom|Hom (A ~ B) F _ (VF1 ~ VF2) (HF1 ~ HF2) HH .↓ =
  B .Hom _ .tran _
  ( (F .f-Mu-bw _ (VF1 × HF2)) ×
    B .Hom _ .tran _
    ( F .f-hom-to _ _ (HH .↓) ×
      F .f-Mu-fw _ (HF1 × VF2) ) )
