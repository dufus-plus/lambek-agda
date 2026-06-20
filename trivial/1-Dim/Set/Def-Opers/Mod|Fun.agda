open import 0-Dim.!quali
open import 1-Dim.Set.Def-Types
open import 1-Dim.Set.Def-Types-pub
open import 1-Dim.Set.Def-Opers.Fun
open import 1-Dim.Set.Def-Opers.Fun-To
open import 1-Dim.Set.Def-Opers.Mod
open import 1-Dim.Set.Def-Opers.Mod-Fun
import 2-Dim.PoSet-Qu.Def-Types.Obj as PoSet-Qu
import 2-Dim.PoSet|PoSet-Qu.Def-Types.Obj as PoSet|PoSet-Qu
import 2-Dim.PoCat.Def-Types.is-Obj as PoCat
import 2-Dim.PoCat|PoCat.Def-Types.is-Obj as PoCat|PoCat
open import 2-Dim.PoCat|PoCat.Def-Types-pub.is-Obj

-- operations in Po(Set)oid on square 2-(Mor)phisms
module 1-Dim.Set.Def-Opers.Mod|Fun where

module _ where
  open import 2-Dim.PoSet|PoSet-Qu.Def-Types-pub.Obj

  Mod|Fun:PQ|PQ : PoSet|PoSet-Qu.[Obj]
  Mod|Fun:PQ|PQ .Ob = [Ob]
  Mod|Fun:PQ|PQ .V-Hom = Fun:Q
  Mod|Fun:PQ|PQ .H-Hom = Mod:PQ
  Mod|Fun:PQ|PQ .H|V-Sqr = [Mod|Fun]

module Mod|Fun where
  open PoSet|PoSet-Qu.[Obj] Mod|Fun:PQ|PQ

  V-oper : PoCat.[oper] PQ|PQ-V:PQ
  H-oper : PoCat.[oper] PQ|PQ-H:PQ
  V-oper = Fun:C.oper
  H-oper = Mod:PC.oper

  V-prop : PoCat.[prop] PQ|PQ-V:PQ V-oper
  H-prop : PoCat.[prop] PQ|PQ-H:PQ H-oper
  V-prop = Fun:C.prop
  H-prop = Mod:PC.prop

  open PoCat|PoCat.:[is-Obj] Mod|Fun:PQ|PQ V-oper H-oper

  Mod-Id|Fun : :H-Id|V
  Mod|Fun-Id : :H|V-Id
  Mod-Mu|Fun : :H-Mu|V
  Mod|Fun-Mu : :H|V-Mu

  Mod-Id|Fun _ f .↓ _ = f .f-to _
  Mod|Fun-Id _ M .↓ _ = ⑴
  Mod-Mu|Fun 23A 3V 22H (HV1 × HV2) .↓ _ (h11 ∙ h12) = HV1 .↓ _ h11 ∙ HV2 .↓ _ h12
  Mod|Fun-Mu 32A 22V 3H (HV1 × HV2) .↓ _ = HV1 .↓ _ ∘ HV2 .↓ _

  I→Mod|Fun : :I→H|V
  Mod→I|Fun : :H→I|V
  Mod|I→Fun : :H|I→V
  Mod|Fun→I : :H|V→I

  I→Mod|Fun (A ~ B) (f1 ~ f2) fto12 .↓ (a1 ~ a2) ato12 = B .tran _ (fto12 .↓ a1 × f2 .f-to _ ato12)
  Mod→I|Fun (A ~ B) (f1 ~ f2) m|f .↓ a = m|f .↓ _ (A .refl a)
  Mod|I→Fun (A ~ B) (M ~ M') mf .↓ = mf .↓
  Mod|Fun→I (A ~ B) (M ~ M') m|f .↓ = m|f .↓

  IMod-Mu|Fun : :IH-Mu|V
  ModI-Mu|Fun : :HI-Mu|V
  Mod|IFun-Mu : :H|IV-Mu
  Mod|FunI-Mu : :H|VI-Mu

  IMod-Mu|Fun 22A 3f (M1 ~ M2) (fto12 × m|f23) .↓ (a11 ~ a12) m1 =
    M2 .lact _ (fto12 .↓ a11 × m|f23 .↓ (a11 ~ a12) m1)
  ModI-Mu|Fun 22A 3f (M1 ~ M2) (m|f12 × fto23) .↓ (a11 ~ a12) m1 =
    M2 .ract _ (m|f12 .↓ (a11 ~ a12) m1 × fto23 .↓ a12)
  Mod|IFun-Mu 22A 2f 3M (mf12 × m|f23) .↓ _ = mf12 .↓ _ ∘ m|f23 .↓ _
  Mod|FunI-Mu 22A 2f 3M (m|f12 × mf23) .↓ _ = m|f12 .↓ _ ∘ mf23 .↓ _

  is-PC|PC : PoCat|PoCat.[is-Obj] DblGraph V-oper H-oper
  is-PC|PC .H-Id|V = Mod-Id|Fun
  is-PC|PC .H|V-Id = Mod|Fun-Id
  is-PC|PC .H-Mu|V = Mod-Mu|Fun
  is-PC|PC .H|V-Mu = Mod|Fun-Mu
  is-PC|PC .I→H|V = I→Mod|Fun
  is-PC|PC .H→I|V = Mod→I|Fun
  is-PC|PC .H|I→V = Mod|I→Fun
  is-PC|PC .H|V→I = Mod|Fun→I
  is-PC|PC .IH-Mu|V = IMod-Mu|Fun
  is-PC|PC .HI-Mu|V = ModI-Mu|Fun
  is-PC|PC .H|IV-Mu = Mod|IFun-Mu
  is-PC|PC .H|VI-Mu = Mod|FunI-Mu

open Mod|Fun using
  (
  Mod-Id|Fun;
  Mod|Fun-Id;
  Mod-Mu|Fun;
  Mod|Fun-Mu;
  I→Mod|Fun;
  Mod→I|Fun;
  Mod|I→Fun;
  Mod|Fun→I;
  IMod-Mu|Fun;
  ModI-Mu|Fun;
  Mod|IFun-Mu;
  Mod|FunI-Mu
  )
