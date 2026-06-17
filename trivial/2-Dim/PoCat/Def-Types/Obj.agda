open import 0-Dim.!quali
import 2-Dim.PoQuiver.Def-Types.Obj as PoQuiver

--
-- (Ob)jects of 2-equipment of 1-(Cat)egories
--
module 2-Dim.PoCat.Def-Types.Obj where

open import 2-Dim.PoCat.Def-Types.is-Obj public

record [Obj] : [Any] where
  constructor ‼

  -- underlying graph
  field It : PoQuiver.[Obj]
  open PoQuiver.[Obj] It public

  -- operations
  field oper : [oper] It
  open [oper] oper public

  -- properties
  field prop : [prop] It oper
  open [prop] prop public
