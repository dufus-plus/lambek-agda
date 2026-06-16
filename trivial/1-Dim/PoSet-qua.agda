--
-- (P)artially (o)rdered (Set)oid
--

-- packaging the modules
module 1-Dim.PoSet-qua where

-- re-export qualified
module PoSet where
  open import 1-Dim.PoSet.Def-Types public
  open import 1-Dim.PoSet.Def-Opers public
  open import 1-Dim.PoSet.Def-Gens public
