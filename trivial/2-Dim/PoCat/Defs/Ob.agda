open import 0-Dim
import 2-Dim.PoSet-Graph.Defs.Ob as PoSet-Graph

--
-- (Ob)jects of 2-equipment of 1-(Cat)egories
--
module 2-Dim.PoCat.Defs.Ob where

open import 2-Dim.PoCat.Defs.is public

record [Ob] : [Any] where
  constructor ‼

  -- underlying graph
  field ↓ : PoSet-Graph.[Ob]
  open PoSet-Graph.[Ob] ↓ public

  -- operations
  field oper : [oper] ↓
  open [oper] oper public

  -- properties
  field prop : [prop] ↓ oper
  open [prop] prop public
