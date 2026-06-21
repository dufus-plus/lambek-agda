open import 0-Dim.!quali

--
-- (Ob)jects of 2-equipment of 1-(Cat)egories
--
module 2-Dim.PoCat.Def-Types.Obj where

open import 2-Dim.PoCat.Def-Types.is-Obj public

record [Obj] : [Any] where
  constructor ‼

  -- data:
  field Ob : [Any]
  field is : [is-Obj] Ob

  -- helpers:
  open [is-Obj] is public

-- define opposites here

open [Obj]

Hom-Opp : [Obj] → [Obj]
Hom-Opp C .Ob = C .Ob
Hom-Opp C .is = Hom-Opp-is _ (C .is)

To-Opp : [Obj] → [Obj]
To-Opp C .Ob = C .Ob
To-Opp C .is = To-Opp-is _ (C .is)
