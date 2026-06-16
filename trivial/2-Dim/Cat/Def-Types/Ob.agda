open import 0-Dim.!quali
import 2-Dim.Quiver.Def-Types.Ob as Quiver

--
-- (Ob)jects of 2-equipment of 1-(Cat)egories
--
module 2-Dim.Cat.Def-Types.Ob where

open import 2-Dim.Cat.Def-Types.is-Ob public

record [Ob] : [Any] where
  constructor ‼

  -- underlying graph
  field It : Quiver.[Ob]
  open Quiver.[Ob] It public

  -- operations
  field oper : [oper] It
  open [oper] oper public

  -- properties
  field prop : [prop] It oper
  open [prop] prop public
