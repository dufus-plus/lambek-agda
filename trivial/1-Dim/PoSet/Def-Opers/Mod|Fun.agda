open import 0-Dim.!quali
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Def-Opers.Fun
open import 1-Dim.PoSet.Def-Opers.Fun-To
open import 1-Dim.PoSet.Def-Opers.Mod
open import 1-Dim.PoSet.Def-Opers.Mod-Fun
import 2-Dim-Pre.AnyPoSet.Def-Types as AnyPoSet
open import 2-Dim-Pre.AnyPoSet.Def-Types-pub
import 2-Dim.PoCat.Def-Types.is-Obj as PoCat
import 2-Dim.PoCat|PoCat.Def-Types.is-Obj as PoCat|PoCat
open import 2-Dim.PoCat|PoCat.Def-Types-pub.is-Obj

-- operations in Po(Set)oid on square 2-(Mor)phisms
module 1-Dim.PoSet.Def-Opers.Mod|Fun where

Mod|Fun:RR : AnyPoSet.[Rel|Rel] _ (2~ Fun) (2~ Mod)
Mod|Fun:RR .Sqr = [Mod|Fun]
Mod|Fun:RR .H-lact _ _ (M1 ~ M2) (fto12 × m|f23) .↓ _ m1 =
  M2 .lact _ (fto12 .↓ _ × m|f23 .↓ _ m1)
Mod|Fun:RR .H-ract _ _ (M1 ~ M2) (m|f12 × fto23) .↓ _ m1 =
  M2 .ract _ (m|f12 .↓ _ m1 × fto23 .↓ _)
Mod|Fun:RR .V-lact _ _ 3M (mf12 × m|f23) .↓ _ = mf12 .↓ _ ∘ m|f23 .↓ _
Mod|Fun:RR .V-ract _ _ 3M (m|f12 × mf23) .↓ _ = m|f12 .↓ _ ∘ mf23 .↓ _

open PoCat|PoCat.:[is-Obj] _ Fun.is-Cat Mod.is-Cat Mod|Fun:RR

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

module Mod|Fun where
  is-Cat : PoCat|PoCat.[is-Obj] _ Fun.is-Cat Mod.is-Cat Mod|Fun:RR
  is-Cat .H-Id|V = Mod-Id|Fun
  is-Cat .H|V-Id = Mod|Fun-Id
  is-Cat .H-Mu|V = Mod-Mu|Fun
  is-Cat .H|V-Mu = Mod|Fun-Mu
  is-Cat .I→H|V = I→Mod|Fun
  is-Cat .H→I|V = Mod→I|Fun
  is-Cat .H|I→V = Mod|I→Fun
  is-Cat .H|V→I = Mod|Fun→I
