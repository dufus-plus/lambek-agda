open import 0-Dim
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Def-Opers.Fun
open import 1-Dim.PoSet.Obj-Types.Adj
open import 1-Dim.PoSet.Gens.Prod

-- universal property of (Top) object
module 1-Dim.PoSet.Obj-Types.Meet where

module _ (A : [Ob]) where
  module _ (oper : [2Fun] ((A × A) > A)) where
    [is-Meet]-Hard = [is-Adj]-Hard _ (Prod.Diag _ ⊣ oper)
    [is-Meet]-Soft = [is-Adj]-Soft _ (Prod.Diag _ ⊣ oper)

  record [has-Meet] : Any where
    constructor ‼
    field oper : [2Fun] ((A × A) > A)
    field is-Hard : [is-Meet]-Hard oper
    field is-Soft : [is-Meet]-Soft oper
