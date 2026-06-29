open import 0-Dim
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Def-Opers.Fun
open import 1-Dim.PoSet.Obj-Types.Adj
open import 1-Dim.PoSet.Gens.Prod

-- universal property of (Top) object
module 1-Dim.PoSet.Obj-Types.Join where

module _ (A : [Ob]) where
  module _ (oper : [2Fun] ((A × A) > A)) where
    [is-Join]-Hard = [is-Adj]-Hard _ (oper ⊣ Prod.Diag _)
    [is-Join]-Soft = [is-Adj]-Soft _ (oper ⊣ Prod.Diag _)

  record [has-Join] : Any where
    constructor ‼
    field oper : [2Fun] ((A × A) > A)
    field is-Hard : [is-Join]-Hard oper
    field is-Soft : [is-Join]-Soft oper
