open import 0-Dim
import 1-Dim.Graph.Defs.Ob as Graph

--
-- define (Set)oid type
--
module 1-Dim.Set.Defs.Ob where

open import 1-Dim.Set.Defs.is public

record [Ob] : [Any] where
  constructor ‼

  -- underlying graph
  field ↓ : Graph.[Ob]
  open Graph.[Ob] ↓ public

  -- axioms
  field is : [is] ↓
  open [is] is public
