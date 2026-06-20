open import 0-Dim.!quali
import 2-Dim.PoSet-Quiver.Def-Types.Obj as PoSet-Quiver
--
-- (Ob)jects of 2-equipment of 1-(Cat)egories
--
module 2-Dim.PoCat.Def-Types.Obj where

open import 2-Dim.PoCat.Def-Types.is-Obj public

open PoSet-Quiver using (‼)

record [Obj] : [Any] where
  constructor ‼

  -- data:
  field Ob : [Any]
  field is : [is-Obj] Ob

  -- helpers:
  open [is-Obj] is public

  Obj→Qu : PoSet-Quiver.[Obj]
  Obj→Qu = ‼ Ob Hom

open [Obj] public
  using (Obj→Qu)
