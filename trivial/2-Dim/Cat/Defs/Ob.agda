open import 0-Dim
import 1-Dim.AnySet.Defs as AnySet
import 1-Dim.Set.Defs as Set
import 2-Dim.Set-Graph.Defs.Ob as Set-Graph

--
-- (Ob)jects of 2-equipment of 1-(Cat)egories
--
module 2-Dim.Cat.Defs.Ob where

open import 2-Dim.Cat.Defs.is public

record [Ob] : [Any] where
  constructor ‼

  -- underlying graph
  field ↓ : Set-Graph.[Ob]
  open Set-Graph.[Ob] ↓ public

  -- operations
  field oper : [oper] ↓
  open [oper] oper public

  -- properties
  field prop : [prop] ↓ oper
  open [prop] prop public
