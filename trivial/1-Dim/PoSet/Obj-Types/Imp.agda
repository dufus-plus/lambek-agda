open import 0-Dim
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Def-Opers.Fun
open import 1-Dim.PoSet.Obj-Types.nAdj
open import 1-Dim.PoSet.Gens.Objs

-- universal property of (Imp)lication operation
module 1-Dim.PoSet.Obj-Types.Imp where

module _ (A : [Ob]) where

  module _ (3op : [2⊣] ((A × A) ~ A) [2Fun]) where
    [is-Imp]-Soft = [is-2Adj]-Soft _ 3op

  record [has-Imp] : [Any] where
    constructor ‼
    field opers : [2⊣] ((A × A) ~ A) [2Fun]
    field is-Soft : [is-Imp]-Soft opers
