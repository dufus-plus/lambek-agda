--
-- define (P)artially (o)rdered (Set)oid
--
module 1-Dim.PoSet where

-- export qualified
module PoSet where
  open import 1-Dim.PoSet.Def-Types public
  open import 1-Dim.PoSet.Def-Opers public
  open import 1-Dim.PoSet.Def-Gens public

-- export un-qualified
open PoSet using (↑; ‼) public
