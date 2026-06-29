open import 0-Dim.!quali
import 2-Dim-Pre.PoSet-Qu.Def-Types as PoSet-Qu

--
-- (Ob)jects of 2-equipment of 1-(Cat)egories
--
module 2-Dim.PoCat.Def-Types.Obj where

open import 2-Dim.PoCat.Def-Types.is-Obj public

open PoSet-Qu using (‼)

record [Obj] : Any where
  constructor ‼

  -- data:
  field Ob : Any
  field is : [is-Obj] Ob

  -- helpers:
  open [is-Obj] is public

  Qu : PoSet-Qu.[Obj]
  Qu = ‼ Ob Hom

open [Obj] public
  using (Qu)

-- define opposites here

open [Obj]

Hom-Opp : [Obj] → [Obj]
Hom-Opp C .Ob = C .Ob
Hom-Opp C .is = Hom-Opp-is _ (C .is)

To-Opp : [Obj] → [Obj]
To-Opp C .Ob = C .Ob
To-Opp C .is = To-Opp-is _ (C .is)
