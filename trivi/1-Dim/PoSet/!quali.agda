--
-- (P)artially (o)rdered (Set)oid
--

-- packaging the modules
module 1-Dim.PoSet.!quali where

-- re-export qualified
module PoSet where
  open import 1-Dim.PoSet.Def-Types public
  open import 1-Dim.PoSet.Def-Opers public
  open import 1-Dim.PoSet.Def-Gens public
  open import 1-Dim.PoSet.Conv public
