open import 0-Dim.!quali
import 2-Dim.Set-Qu.Def-Types.Obj as Set-Qu

--
-- (Ob)jects of 2-equipment of 1-(Cat)egories
--
module 2-Dim.Cat.Def-Types.Obj where

open import 2-Dim.Cat.Def-Types.is-Obj public

record [Obj] : [Any] where
  constructor ‼

  -- underlying graph
  field It : Quiver.[Obj]
  open Quiver.[Obj] It public

  -- operations
  field oper : [oper] It
  open [oper] oper public

  -- properties
  field prop : [prop] It oper
  open [prop] prop public
