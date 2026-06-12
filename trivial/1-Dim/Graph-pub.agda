open import 0-Dim

module 1-Dim.Graph-pub where

-- re-export qualified
module Graph where
  open import 1-Dim.Graph.Def-Types public
  open import 1-Dim.Graph.Def-Opers public
  open import 1-Dim.Graph.Gens public

open Graph using (↑; ‼) public
open import 1-Dim.Graph.Def-Types-pub public
