--
-- define (Set)oids
--

-- packaging the modules
module 1-Dim.Set-qua where

-- re-export qualified
module Set where
  open import 1-Dim.Set.Def-Types public
  open import 1-Dim.Set.Def-Opers public
  open import 1-Dim.Set.Def-Gens public
