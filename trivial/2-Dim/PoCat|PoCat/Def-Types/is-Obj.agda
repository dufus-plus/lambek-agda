open import 0-Dim.!quali
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet
import 1-Dim.PoSet.Def-Types as PoSet
open import 1-Dim.PoSet.Def-Types-pub
import 2-Dim.PoSet-Qu.Def-Types.Obj as PoSet-Qu
import 2-Dim.PoSet-Qu|PoSet-Qu.Def-Types.Obj as PoSet-Qu|PoSet-Qu
open import 2-Dim.PoSet-Qu|PoSet-Qu.Def-Types-pub.Obj
import 2-Dim.PoCat.Def-Types.is-Obj as PoCat

module 2-Dim.PoCat|PoCat.Def-Types.is-Obj where

open PoCat using (‼)
open PoSet-Qu|PoSet-Qu using (‼)

module :[is-Obj]
       (PQ|PQ : PoSet-Qu|PoSet-Qu.[Obj]) (open PoSet-Qu|PoSet-Qu.[Obj] PQ|PQ)
       (V-oper @(‼ VId VMu): PoCat.[oper] V:PQ)
       (H-oper @(‼ HId HMu): PoCat.[oper] H:PQ) where

  HMuEl : Any.Rel-[2-Fun] _ ((H-El × H-El) ~ H-El)
  HMuEl 3o 2h = HMu 3o .f-el 2h
  VMuEl : Any.Rel-[2-Fun] _ ((V-El × V-El) ~ V-El)
  VMuEl 3o 2v = VMu 3o .f-el 2v

  :H-Id|V : [Any]
  :H|V-Id : [Any]
  :H-Mu|V : [Any]
  :H|V-Mu : [Any]

  :H-Id|V = Any.Rel|Rel-[0₁-Fun] _ _ _ (! ~ H|V-Mor) (2~ HId)
  :H|V-Id = Any.Rel|Rel-[0₂-Fun] _ _ _ (! ~ H|V-Mor) (2~ VId)
  :H-Mu|V = Any.Rel|Rel-[2₁-Fun] _ _ _ ((H|V-Mor × H|V-Mor) ~ H|V-Mor) (2~ HMuEl)
  :H|V-Mu = Any.Rel|Rel-[2₂-Fun] _ _ _ ((H|V-Mor × H|V-Mor) ~ H|V-Mor) (2~ VMuEl)

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

module _ (PQ|PQ : PoSet-Qu|PoSet-Qu.[Obj]) (open PoSet-Qu|PoSet-Qu.[Obj] PQ|PQ)
         (V-oper : PoCat.[oper] V:PQ)
         (H-oper : PoCat.[oper] H:PQ) where
  record [is-Obj] : [Any] where
    constructor ‼
    open :[is-Obj] PQ|PQ V-oper H-oper

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

    -- glob/cube action (transport)
    field IH-Mu|V : :IH-Mu|V
    field HI-Mu|V : :HI-Mu|V
    field H|IV-Mu : :H|IV-Mu
    field H|VI-Mu : :H|VI-Mu
