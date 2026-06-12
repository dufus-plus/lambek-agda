open import 0-Dim
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Def-Opers.Fun
open import 1-Dim.PoSet.Obj-Types.Adj
open import 1-Dim.PoSet.Gens.Unit

-- universal property of (Top) object
module 1-Dim.PoSet.Obj-Types.Top where

module _ (A : [Ob]) where
  module _  (oper : [0Fun] (! > A)) where
    [is-Top]-Hard = [is-Adj]-Hard _ (Unit.Term _ ⊣ oper)
    [is-Top]-Soft = [is-Adj]-Soft _ (Unit.Term _ ⊣ oper)

  record [has-Top] : [Any] where
    constructor ‼
    field oper : [0Fun] (! > A)
    field is-Hard : [is-Top]-Hard oper
    field is-Soft : [is-Top]-Soft oper
