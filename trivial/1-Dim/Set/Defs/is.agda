open import 0-Dim
import 1-Dim.Graph.Defs.Ob as Graph

--
-- define (Set)oid type
--
module 1-Dim.Set.Defs.is where

open Graph using (‼)

module :is (Graph @(‼ Ob To) : Graph.[Ob]) where
  -- axioms of equivalence
  :refl = Any.Rel-[0Fun] _ ( !        > To)
  :symm = Any.Rel-[-Fun] _ ((- To)    > To)
  :tran = Any.Rel-[2Fun] _ ((To × To) > To)

record [is] (Graph : Graph.[Ob]) : [Any] where
  constructor ‼
  open :is Graph
  field refl : :refl
  field symm : :symm
  field tran : :tran
