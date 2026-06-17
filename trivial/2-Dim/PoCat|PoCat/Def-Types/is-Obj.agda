open import 0-Dim.!quali
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet
import 1-Dim.PoSet.Def-Types as PoSet
open import 1-Dim.PoSet.Def-Types-pub
import 2-Dim.PoQuiver.Def-Types.Obj as PoQuiver
import 2-Dim.PoQuiver|PoQuiver.Def-Types.Obj as PoQuiver|PoQuiver
open import 2-Dim.PoQuiver|PoQuiver.Def-Types-pub.Obj
import 2-Dim.PoCat.Def-Types.is-Obj as PoCat

module 2-Dim.PoCat|PoCat.Def-Types.is-Obj where

open PoCat using (‼)
open PoQuiver|PoQuiver using (‼)

module :[is-Obj]
       (DblQuiver @(‼ $Ob V-Mor H-Mor H|V-Mor) : PoQuiver|PoQuiver.[Obj])
       (V-oper @(‼ VId VMu): PoCat.[oper] (V-Graph DblQuiver))
       (H-oper @(‼ HId HMu): PoCat.[oper] (H-Graph DblQuiver))
    where

  :H-Id|V : [Any]
  :H|V-Id : [Any]
  :H-Mu|V : [Any]
  :H|V-Mu : [Any]

  :H-Id|V = (2ob : [2~] $Ob) → (V : V-Mor 2ob .El) → H|V-Mor _ (V ~ V) (HId _ ~ HId _)

  :H|V-Id = (2ob : [2~] $Ob) → (H : H-Mor 2ob .El) → H|V-Mor _ (VId _ ~ VId _) (H ~ H)

  :H-Mu|V = (23ob @((ob11 ~ ob12 ~ ob13) ~ (ob21 ~ ob22 ~ ob23)): [23~] $Ob) →
    (3V @(V1 ~ V2 ~ V3) :
        V-Mor (ob11 ~ ob21) .El [~] V-Mor (ob12 ~ ob22) .El [~] V-Mor (ob13 ~ ob23) .El)
    (22H @((H11 × H12) ~ (H21 × H22)) :
           (H-Mor (ob11 ~ ob12) .El [×] H-Mor (ob12 ~ ob13) .El) [~]
           (H-Mor (ob21 ~ ob22) .El [×] H-Mor (ob22 ~ ob23) .El)) →
    (2HV : H|V-Mor _ (V1 ~ V2) (H11 ~ H21) [×]
           H|V-Mor _ (V2 ~ V3) (H12 ~ H22)) →
           H|V-Mor _ (V1 ~ V3) (HMu _ .f-ob (H11 × H12) ~ HMu _ .f-ob (H21 × H22))

  :H|V-Mu = (32ob @((ob11 ~ ob12) ~ (ob21 ~ ob22) ~ (ob31 ~ ob32)): [32~] $Ob) →
    (22V @((V11 × V21) ~ (V12 × V22)) :
           (V-Mor (ob11 ~ ob21) .El [×] V-Mor (ob21 ~ ob31) .El) [~]
           (V-Mor (ob12 ~ ob22) .El [×] V-Mor (ob22 ~ ob32) .El)) →
    (3H @(H1 ~ H2 ~ H3) :
        H-Mor (ob11 ~ ob12) .El [~] H-Mor (ob21 ~ ob22) .El [~] H-Mor (ob31 ~ ob32) .El)
    (2HV : H|V-Mor _ (V11 ~ V12) (H1 ~ H2) [×]
           H|V-Mor _ (V21 ~ V22) (H2 ~ H3)) →
           H|V-Mor _ (VMu _ .f-ob (V11 × V21) ~ VMu _ .f-ob (V12 × V22)) (H1 ~ H3)

  :I→H|V : [Any]
  :H→I|V : [Any]
  :H|I→V : [Any]
  :H|V→I : [Any]

  :I→H|V = (2ob : [2~] $Ob) → (2V : [2~] V-Mor 2ob .El) →
            V-Mor _ .To 2V → H|V-Mor _ 2V (HId _ ~ HId _)

  :H→I|V = (2ob : [2~] $Ob) → (2V : [2~] V-Mor 2ob .El) →
            H|V-Mor _ 2V (HId _ ~ HId _) → V-Mor _ .To 2V

  :H|I→V = (2ob : [2~] $Ob) → (2H : [2~] H-Mor 2ob .El) →
            H-Mor _ .To 2H → H|V-Mor _ (VId _ ~ VId _) 2H

  :H|V→I = (2ob : [2~] $Ob) → (2H : [2~] H-Mor 2ob .El) →
            H|V-Mor _ (VId _ ~ VId _) 2H → H-Mor _ .To 2H

  :IH-Mu|V : [Any]
  :HI-Mu|V : [Any]
  :H|IV-Mu : [Any]
  :H|VI-Mu : [Any]

  :IH-Mu|V = (22ob @((ob11 ~ ob12) ~ (ob21 ~ ob22)): [22~] $Ob) →
    (3V @(V1 ~ V2 ~ V3) :
        V-Mor (ob11 ~ ob21) .El [~] V-Mor (ob11 ~ ob21) .El [~] V-Mor (ob12 ~ ob22) .El)
    (2H @(H1 ~ H2) :
           (H-Mor (ob11 ~ ob12) .El) [~] (H-Mor (ob21 ~ ob22) .El)) →
    (2HV : V-Mor _ .To (V1 ~ V2) [×]
           H|V-Mor _ (V2 ~ V3) (H1 ~ H2)) →
           H|V-Mor _ (V1 ~ V3) (H1 ~ H2)

  :HI-Mu|V = (22ob @((ob11 ~ ob12) ~ (ob21 ~ ob22)): [22~] $Ob) →
    (3V @(V1 ~ V2 ~ V3) :
        V-Mor (ob11 ~ ob21) .El [~] V-Mor (ob12 ~ ob22) .El [~] V-Mor (ob12 ~ ob22) .El)
    (2H @(H1 ~ H2) :
           (H-Mor (ob11 ~ ob12) .El) [~] (H-Mor (ob21 ~ ob22) .El)) →
    (2HV : H|V-Mor _ (V1 ~ V2) (H1 ~ H2) [×]
           V-Mor _ .To (V2 ~ V3)) →
           H|V-Mor _ (V1 ~ V3) (H1 ~ H2)

  :H|IV-Mu = (22ob @((ob11 ~ ob12) ~ (ob21 ~ ob22)): [22~] $Ob) →
    (2V @(V1 ~ V2) :
           (V-Mor (ob11 ~ ob21) .El) [~] (V-Mor (ob12 ~ ob22) .El)) →
    (3H @(H1 ~ H2 ~ H3) :
        H-Mor (ob11 ~ ob12) .El [~] H-Mor (ob11 ~ ob12) .El [~] H-Mor (ob21 ~ ob22) .El)
    (2HV : H-Mor _ .To (H1 ~ H2) [×]
           H|V-Mor _ (V1 ~ V2) (H2 ~ H3)) →
           H|V-Mor _ (V1 ~ V2) (H1 ~ H3)

  :H|VI-Mu = (22ob @((ob11 ~ ob12) ~ (ob21 ~ ob22)): [22~] $Ob) →
    (2V @(V1 ~ V2) :
           (V-Mor (ob11 ~ ob21) .El) [~] (V-Mor (ob12 ~ ob22) .El)) →
    (3H @(H1 ~ H2 ~ H3) :
        H-Mor (ob11 ~ ob12) .El [~] H-Mor (ob21 ~ ob22) .El [~] H-Mor (ob21 ~ ob22) .El)
    (2HV : H|V-Mor _ (V1 ~ V2) (H1 ~ H2) [×]
           H-Mor _ .To (H2 ~ H3)) →
           H|V-Mor _ (V1 ~ V2) (H1 ~ H3)

module _ (DblGraph : PoQuiver|PoQuiver.[Obj])
         (V-oper : PoCat.[oper] (V-Graph DblGraph))
         (H-oper : PoCat.[oper] (H-Graph DblGraph))
      where
  record [is-Obj] : [Any] where
    constructor ‼
    open :[is-Obj] DblGraph V-oper H-oper

    -- cube composites
    field H-Id|V : :H-Id|V
    field H|V-Id : :H|V-Id
    field H-Mu|V : :H-Mu|V
    field H|V-Mu : :H|V-Mu

    -- glob/cube conversion
    field I→H|V : :I→H|V
    field H→I|V : :H→I|V
    field H|I→V : :H|I→V
    field H|V→I : :H|V→I

    -- glob/cube action
    field IH-Mu|V : :IH-Mu|V
    field HI-Mu|V : :HI-Mu|V
    field H|IV-Mu : :H|IV-Mu
    field H|VI-Mu : :H|VI-Mu
