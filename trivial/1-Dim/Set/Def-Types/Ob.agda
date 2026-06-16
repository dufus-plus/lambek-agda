open import 0-Dim.!quali
import 1-Dim.Graph.Def-Types.Ob as Graph

--
-- define (Set)oid type
--
module 1-Dim.Set.Def-Types.Ob where

open import 1-Dim.Set.Def-Types.is-Ob public

record [Ob] : [Any] where
  constructor ‼

  -- underlying graph
  field It : Graph.[Ob]
  open Graph.[Ob] It public

  -- axioms
  field is : [is-Ob] It
  open [is-Ob] is public
