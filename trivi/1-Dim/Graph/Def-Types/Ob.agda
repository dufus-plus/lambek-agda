open import 0-Dim.!quali

--
-- define (Gra)ph type
--
module 1-Dim.Graph.Def-Types.Ob where

module :[Ob] where
  -- objects
  module _ (El : Any) where
    -- the relation
    :To = Any.[Rel] (2~ El)

record [Ob] : Any where
  constructor ‼
  open :[Ob]
  field El : Any
  field To : :To El

open [Ob]

-- the (Opp)osite Graph
module _ (A : [Ob]) where
  To-Opp : [Ob]
  To-Opp .El = A .El
  To-Opp .To = Any.Rel-Op _ (A .To)
