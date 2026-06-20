open import 0-Dim.!quali
import 2-Dim-Pre.Set-Qu.Def-Types.Obj as Set-Qu
--
-- (Ob)jects of 2-equipment of 1-(Cat)egories
--
module 2-Dim.Cat.Def-Types.Obj where

open import 2-Dim.Cat.Def-Types.is-Obj public

open Set-Qu using (‼)

record [Obj] : [Any] where
  constructor ‼

  -- data:
  field Ob : [Any]
  field is : [is-Obj] Ob

  -- helpers:
  open [is-Obj] is public
