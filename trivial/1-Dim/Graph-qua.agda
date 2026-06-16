-- packaging the modules
module 1-Dim.Graph-qua where

-- re-export qualified
module Graph where
  open import 1-Dim.Graph.Def-Types public
  open import 1-Dim.Graph.Def-Opers public
  open import 1-Dim.Graph.Def-Gens public
