open import 0-Dim
import 1-Dim.PoSet.Defs as PoSet
import 2-Dim.PoSet-DblGraph.Defs.Ob as PoSet-DblGraph
open import 2-Dim.PoCat.Defs.Ob
open import 2-Dim.PoCat.Defs.Fun
open import 2-Dim.PoCat.Defs.Hom
open import 2-Dim.PoCat.Defs.Hom|Hom
import 2-Dim.DblCat.Defs.is as DblCat

module 2-Dim.PoCat.Oper.Hom|Hom where

open PoSet-DblGraph.[Ob]
open [Ob]
open [Fun]
open PoSet.[Ob]
open PoSet.[Fun]
open [Hom|Hom]

module Hom|Hom (C : [Ob]) where
  DblGraph : PoSet-DblGraph.[Ob]
  DblGraph .HV-Ob = C .Ob -- PoSet
  DblGraph .V-Mor = C .Hom
  DblGraph .H-Mor = C .Hom
  DblGraph .H|V-2Mor = [Hom|Hom] C

  V-oper : [oper] (V-Graph DblGraph)
  H-oper : [oper] (H-Graph DblGraph)
  V-oper = C .oper
  H-oper = C .oper

  V-prop : [prop] (V-Graph DblGraph) V-oper
  H-prop : [prop] (H-Graph DblGraph) H-oper
  V-prop = C .prop
  H-prop = C .prop

  open DblCat.:is DblGraph V-oper H-oper
-- Hom-[To] C _ (Hom-Mu C _ (VF1 × HF2) ~ Hom-Mu C _ (HF1 × VF2))

  Hom-Id|Hom : :H-Id|V
  Hom|Hom-Id : :H|V-Id
  Hom-Mu|Hom : :H-Mu|V
  Hom|Hom-Mu : :H|V-Mu

  Hom-Id|Hom _ V .↓ = C .Hom _ .tran _ (C .RUnit-bw _ V × C .LUnit-fw _ V)
  Hom|Hom-Id _ H .↓ = C .Hom _ .tran _ (C .LUnit-bw _ H × C .RUnit-fw _ H)

  Hom-Mu|Hom _ (V1 ~ V2 ~ V3) ((H11 × H12) ~ (H21 × H22)) (hv1 × hv2) .↓ =
    C .Hom _ .tran _
      (C .Assoc-bw _ (V1 × H21 × H22) ×
      C .Hom _ .tran _
        ((C .Mu _ .f-to _ (hv1 .↓ × C .Hom _ .refl H22)) ×
        C .Hom _ .tran _
          ((C .Assoc-fw _ (H11 × V2 × H22)) ×
          C .Hom _ .tran _
            (C .Mu _ .f-to _ (C .Hom _ .refl H11 × hv2 .↓) ×
            C .Assoc-bw _ (H11 × H12 × V3)))))

  Hom|Hom-Mu _ ((V11 × V21) ~ (V12 × V22)) (H1 ~ H2 ~ H3) (hv1 × hv2) .↓ =
    C .Hom _ .tran _
      (C .Assoc-fw _ (V11 × V21 × H3) ×
      C .Hom _ .tran _
        ((C .Mu _ .f-to _ (C .Hom _ .refl V11 × hv2 .↓)) ×
        C .Hom _ .tran _
          ((C .Assoc-bw _ (V11 × H2 × V22)) ×
          C .Hom _ .tran _
            (C .Mu _ .f-to _ (hv1 .↓ × C .Hom _ .refl V22) ×
            C .Assoc-fw _ (H1 × V12 × V22)))))

open Hom|Hom public
  using
  (
    Hom-Id|Hom;
    Hom|Hom-Id;
    Hom-Mu|Hom;
    Hom|Hom-Mu
  )

F-Hom|Hom :
  (2C@(A ~ B) : [2~] [Ob])
  (F : [Fun] 2C) →
  (22ob : [22~] A. Ob)
  (2VF @(VF1 > VF2) : [Dup|Hom] A 22ob)
  (2HF @(HF1 ~ HF2) : [Hom|Dup] A 22ob)
  (HH : [Hom|Hom] A _ 2VF 2HF) →
  [Hom|Hom] B _
    (F .F-Hom _ .f-ob VF1 ~ F .F-Hom _ .f-ob VF2)
    (F .F-Hom _ .f-ob HF1 ~ F .F-Hom _ .f-ob HF2)
F-Hom|Hom (A ~ B) F _ (VF1 ~ VF2) (HF1 ~ HF2) HH .↓ =
  B .Hom _ .tran _
  ( (F .F-Mu-bw _ (VF1 × HF2)) ×
    B .Hom _ .tran _
    ( (F .F-Hom _ .f-to _ (HH .↓)) ×
      (F .F-Mu-fw _ (HF1 × VF2)) ) )
