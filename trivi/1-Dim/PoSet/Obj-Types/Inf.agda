open import 0-Dim
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Def-Opers.Fun
open import 1-Dim.PoSet.Obj-Types.Adj
open import 1-Dim.PoSet.Gens.Prod

-- universal property of (Top) object
module 1-Dim.PoSet.Obj-Types.Inf where

module _ (I : Any) (A : [Ob]) where
  module _ (oper : [Fun] (Pow (I > A) > A)) where
    [is-Inf]-Hard = [is-Adj]-Hard _ (Prod.Diag _ ⊣ oper)
    [is-Inf]-Soft = [is-Adj]-Soft _ (Prod.Diag _ ⊣ oper)

  record [has-Inf] : Any where
    constructor ‼
    field oper : [Fun] (Pow (I > A) > A)
    field is-Hard : [is-Meet]-Hard oper
    field is-Soft : [is-Meet]-Soft oper
