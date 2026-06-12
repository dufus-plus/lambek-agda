open import 0-Dim
import 1-Dim.Graph.Def-Types.Ob as Graph

--
-- define Po(Set)oid type
--
module 1-Dim.PoSet.Def-Types.Ob where

open import 1-Dim.PoSet.Def-Types.is public

record [Ob] : [Any] where
  constructor ‼

  -- underlying graph
  field ↓ : Graph.[Ob]
  open Graph.[Ob] ↓ public

  -- axioms
  field is : [is] ↓
  open [is] is public
