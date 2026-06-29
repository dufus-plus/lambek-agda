open import 0-Dim.!quali
import 1-Dim.Graph.Def-Types.Ob as Graph

--
-- define Po(Set)oid type as underlying carrier and structure
--
module 1-Dim.PoSet.Def-Types.Ob where

open import 1-Dim.PoSet.Def-Types.is-Ob public

record [Ob] : Any where
  constructor ‼

  -- underlying graph
  field It : Graph.[Ob]
  open Graph.[Ob] It public

  -- axioms
  field is : [is-Ob] It
  open [is-Ob] is public

open [Ob]
open [is-Ob]

-- the (Opp)osite PoSetoid
module _ (A : [Ob]) where
  To-Opp : [Ob]
  To-Opp .It = Graph.To-Opp (A .It)
  To-Opp .is .refl _ = A .refl _
  To-Opp .is .tran _ ((ato21) × (ato32)) = A .tran _ (ato32 × ato21)
