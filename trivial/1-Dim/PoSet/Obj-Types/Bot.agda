open import 0-Dim
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Def-Opers.Fun
open import 1-Dim.PoSet.Obj-Types.Adj
open import 1-Dim.PoSet.Gens.Unit

-- universal property of (Bot)tom object
module 1-Dim.PoSet.Obj-Types.Bot where

module _ (A : [Ob]) where
  module _  (oper : [0Fun] (! > A)) where
    [is-Bot]-Hard = [is-Adj]-Hard _ (oper ⊣ Unit.Term _)
    [is-Bot]-Soft = [is-Adj]-Soft _ (oper ⊣ Unit.Term _)

  -- redundant definition
  record [has-Bot] : [Any] where
    constructor ‼
    field oper : [0Fun] (! > A)
    field is-Hard : [is-Bot]-Hard oper
    field is-Soft : [is-Bot]-Soft oper
