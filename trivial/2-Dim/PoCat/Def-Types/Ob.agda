open import 0-Dim.!quali
import 2-Dim.PoQuiver.Def-Types.Ob as PoQuiver

--
-- (Ob)jects of 2-equipment of 1-(Cat)egories
--
module 2-Dim.PoCat.Def-Types.Ob where

open import 2-Dim.PoCat.Def-Types.is-Ob public

record [Ob] : [Any] where
  constructor ‼

  -- underlying graph
  field It : PoQuiver.[Ob]
  open PoQuiver.[Ob] It public

  -- operations
  field oper : [oper] It
  open [oper] oper public

  -- properties
  field prop : [prop] It oper
  open [prop] prop public
