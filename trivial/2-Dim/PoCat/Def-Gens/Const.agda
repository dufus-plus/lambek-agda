open import 0-Dim
open import 1-Dim.PoSet
open import 1-Dim.Graph
open import 2-Dim.PoCat.Defs.Ob
open import 2-Dim.PoCat.Defs.Fun
open import 2-Dim.PoCat.Defs.Fun-Hom
open import 2-Dim.PoCat.Defs.Fun-Hom-To
open import 2-Dim.PoCat.Gens.Fun
open import 2-Dim.PoCat.Oper.Hom|Hom
import 2-Dim.PoSet-Graph.Defs.Fun as PoSet-Graph


module 2-Dim.PoCat.Gens.Const where

open [Ob]
open [Fun]
open [is-Fun]
open Fun-[Hom]
open Fun-Hom-[To]
open PoSet.[Ob]
open PoSet.[Fun]
open Graph.[Fun]
open PoSet-Graph.[Fun]

module _ (2C @(A > B) : [2~] [Ob]) where
  Const : B .Ob → [Fun] (A > B)
  Const b .↓ .f-el = Any.Const _ b
  Const b .↓ .F-Hom _ = PoSet.Const _ (B .Id b)
  Const b .is .F-Id-fw _ = B .Hom _ .refl _
  Const b .is .F-Id-bw _ = B .Hom _ .refl _
  Const b .is .F-Mu-fw _ (h12 × h23) = B .bunit-fw _
  Const x .is .F-Mu-bw _ (h12 × h23) = B .bunit-bw _

  Const:F : [Fun] (B > Fun (A > B))
  Const:F .↓ .f-el = Const
  Const:F .↓ .F-Hom 2b .↓ .f-el bhom .n-ob _ = bhom
  Const:F .↓ .F-Hom 2b .↓ .f-el bhom .n-hom-fw _ _ = Hom-Id|Hom B _ bhom
  Const:F .↓ .F-Hom 2b .↓ .f-el bhom .n-hom-bw _ _ = Hom|Hom-Id B _ bhom
  Const:F .↓ .F-Hom 2b .↓ .f-to _ bto .↓ _ = bto
  Const:F .is .F-Id-fw _ .↓ _ = B .Hom _ .refl _
  Const:F .is .F-Id-bw _ .↓ _ = B .Hom _ .refl _
  Const:F .is .F-Mu-fw _ (bhom12 × bhom23) .↓ _ = B .Hom _ .refl _
  Const:F .is .F-Mu-bw _ (bhom12 × bhom23) .↓ _ = B .Hom _ .refl _
