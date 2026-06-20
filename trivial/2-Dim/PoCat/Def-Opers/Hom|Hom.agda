open import 0-Dim.!quali
open import 1-Dim.PoSet.!publi
open import 2-Dim.PoCat.Def-Types
open import 2-Dim.PoCat.Def-Types-pub
import 2-Dim-Pre.Matr.Def-Types as AnyPoSet
open import 2-Dim-Pre.Matr.Def-Types-pub
import 2-Dim.PoCat|PoCat.Def-Types.is-Obj as PoCat|PoCat

module 2-Dim.PoCat.Def-Opers.Hom|Hom
  (C : [Obj]) (let module C = [Obj] C) where

module Hom|Hom where
  [Hom|Hom]:Mod : Matr.[PoSet|PoSet] _ (2~ C.Hom) (2~ C.Hom)
  [Hom|Hom]:Mod .Sqr = [Hom|Hom] C
  [Hom|Hom]:Mod .H-lact = _
  [Hom|Hom]:Mod .H-ract = _
  [Hom|Hom]:Mod .V-lact = _
  [Hom|Hom]:Mod .V-ract = _
  -- TODO

  open PoCat|PoCat.:[is-Obj] C.Ob C.is C.is [Hom|Hom]:Mod
  -- C .Hom-To _ (C .Mu-el _ (VF1 × HF2) ~ C .Mu-el _ (HF1 × VF2))

  Hom-Id|Hom : :H-Id|V
  Hom|Hom-Id : :H|V-Id
  Hom-Mu|Hom : :H-Mu|V
  Hom|Hom-Mu : :H|V-Mu

  Hom-Id|Hom _ V .↓ = C.Hom-tran _ _ (C.runit-bw _ V × C.lunit-fw _ V)
  Hom|Hom-Id _ H .↓ = C.Hom-tran _ _ (C.lunit-bw _ H × C.runit-fw _ H)

  Hom-Mu|Hom _ (V1 ~ V2 ~ V3) ((H11 × H12) ~ (H21 × H22)) (hv1 × hv2) .↓ =
    C.Hom _ .tran _
      (C.assoc-bw _ (V1 × H21 × H22) ×
      C.Hom _ .tran _
        ((C.Mu _ .f-to _ (hv1 .↓ × C.Hom _ .refl H22)) ×
        C.Hom _ .tran _
          ((C.assoc-fw _ (H11 × V2 × H22)) ×
          C.Hom _ .tran _
            (C.Mu _ .f-to _ (C.Hom _ .refl H11 × hv2 .↓) ×
            C.assoc-bw _ (H11 × H12 × V3)))))

  Hom|Hom-Mu _ ((V11 × V21) ~ (V12 × V22)) (H1 ~ H2 ~ H3) (hv1 × hv2) .↓ =
    C.Hom _ .tran _
      (C.assoc-fw _ (V11 × V21 × H3) ×
      C.Hom _ .tran _
        ((C.Mu _ .f-to _ (C.Hom _ .refl V11 × hv2 .↓)) ×
        C.Hom _ .tran _
          ((C.assoc-bw _ (V11 × H2 × V22)) ×
          C.Hom _ .tran _
            (C.Mu _ .f-to _ (hv1 .↓ × C.Hom _ .refl V22) ×
            C.assoc-fw _ (H1 × V12 × V22)))))

open Hom|Hom public
  using
  ( Hom-Id|Hom;
    Hom|Hom-Id;
    Hom-Mu|Hom;
    Hom|Hom-Mu )

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
