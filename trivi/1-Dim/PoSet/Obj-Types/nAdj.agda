open import 0-Dim
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Def-Opers.Fun
open import 1-Dim.PoSet.Def-Opers.Rep
open import 1-Dim.PoSet.Gens.Objs

module 1-Dim.PoSet.Obj-Types.nAdj where

module _ (3C @((A × B) ~ C) : ([2×] [Ob]) [~] [Ob]) where
  record [2⊣] (2F : ([2×] [Ob]) [~] [Ob] → Any) : Any where
    constructor 2⊣
    field ⊗ : 2F ((A × B) > C)
    field ⇒ : 2F ((Opp A × A) > A)
    field ⇐ : 2F ((A × Opp A) > A)

  module _ (3f @(2⊣ ⊗ ⇒ ⇐) : [2⊣] [2Fun]) where
    record [is-2Adj]-Soft : Any where
      constructor ‼
      -- TODO 2Rep

  record [2Adj] : Any where
    constructor ‼
    field ↓ : [2⊣] [2Fun]
    field is-Soft : [is-2Adj]-Soft ↓
