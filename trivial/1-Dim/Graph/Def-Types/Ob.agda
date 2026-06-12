open import 0-Dim

--
-- define (Gra)ph type
--
module 1-Dim.Graph.Def-Types.Ob where

module :[Ob] where
  -- objects
  :Ob = Any.[Ob]
  module _ (Ob : :Ob) where
    -- the relation
    :To = Any.[Rel] (2~ Ob)

record [Ob] : [Any] where
  constructor ‼
  open :[Ob]
  field Ob : :Ob
  field To : :To Ob
