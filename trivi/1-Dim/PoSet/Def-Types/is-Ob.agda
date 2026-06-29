open import 0-Dim.!quali
import 1-Dim.Graph.Def-Types.Ob as Graph

--
-- pre define Po(Set)oid type as structure on Graph
--
module 1-Dim.PoSet.Def-Types.is-Ob where

open Graph using (‼)

module :[is-Ob] (Graph @(‼ Ob To) : Graph.[Ob]) where
  -- axioms of equivalence
  :refl = Any.Rel-[0-Fun] _ ( !        > To)
  :tran = Any.Rel-[2-Fun] _ ((To × To) > To)

record [is-Ob] (Graph : Graph.[Ob]) : Any where
  constructor ‼
  open :[is-Ob] Graph
  field refl : :refl
  field tran : :tran
