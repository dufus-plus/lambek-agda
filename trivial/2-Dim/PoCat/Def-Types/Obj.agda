open import 0-Dim.!quali
import 2-Dim-Pre.PoSet-Qu.Def-Types.Obj as PoSet-Qu
--
-- (Ob)jects of 2-equipment of 1-(Cat)egories
--
module 2-Dim.PoCat.Def-Types.Obj where

open import 2-Dim.PoCat.Def-Types.is-Obj public

open PoSet-Qu using (‼)

record [Obj] : [Any] where
  constructor ‼

  -- data:
  field Ob : [Any]
  field is : [is-Obj] Ob

  -- helpers:
  open [is-Obj] is public
