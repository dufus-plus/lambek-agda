open import 0-Dim.!quali
open import 1-Dim.Graph.!publi
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Def-Opers.Fun

module 1-Dim.PoSet.Def-Gens.Const where

module _ (2O @(A ~ B) : [2~] [Ob]) where
  Const : B .El → [Fun] (A > B)
  Const b .↓ .f-el = Any.Const _ b
  Const b .↓ .f-to _ _ = B .refl b

  Const:F : [Fun] (B > Fun (A > B))
  Const:F .↓ .f-el = Const
  Const:F .↓ .f-to _ bto12 .↓ _ = bto12
