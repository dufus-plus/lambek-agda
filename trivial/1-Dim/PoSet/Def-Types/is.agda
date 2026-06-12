open import 0-Dim
import 1-Dim.Graph.Def-Types.Ob as Graph

--
-- pre define Po(Set)oid structure type
--
module 1-Dim.PoSet.Def-Types.is where

open Graph using (‼)

module :is (Graph @(‼ Ob To) : Graph.[Ob]) where
  -- axioms of equivalence
  :refl = Any.Rel-[0Fun] _ ( !        > To)
  :tran = Any.Rel-[2Fun] _ ((To × To) > To)

record [is] (Graph : Graph.[Ob]) : [Any] where
  constructor ‼
  open :is Graph
  field refl : :refl
  field tran : :tran
