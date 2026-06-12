open import 0-Dim
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Def-Opers.Fun
open import 1-Dim.PoSet.Def-Opers.Rep

module 1-Dim.PoSet.Obj-Types.Adj where

module _ (2C @(A ~ B) : [2~] [Ob]) where
  module _ (L⊣R @ (L ⊣ R) : [⊣] [Fun] 2C) where

    record [is-Adj]-Hard : [Any] where
      constructor ‼
      field unit+ : Fun-[To] _ (Fun-Id _ > Fun-Mu _ .f-ob (L × R))
      field unit- : Fun-[To] _ (Fun-Mu _ .f-ob (R × L) > Fun-Id _)

    record [is-Adj]-Soft : [Any] where
      constructor ‼
      field fw : Mod-[Fun] _ (Rep+ _ L > Rep- _ (- R))
      field bw : Mod-[Fun] _ (Rep- _ (- R) > Rep+ _ L)

  record [Adj] : [Any] where
    constructor ‼
    field ↓ : [⊣] [Fun] 2C
    field is-Hard : [is-Adj]-Hard ↓
    field is-Soft : [is-Adj]-Soft ↓
