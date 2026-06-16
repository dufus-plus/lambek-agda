--
-- (P)artially (o)rdered (Set)oid
--

-- packaging the modules
module 1-Dim.PoSet-pub where

-- base package
open import 1-Dim.PoSet-qua public

-- re-export the constructors & fields of records
open PoSet using (↑; ‼) public
open import 1-Dim.PoSet.Def-Types-pub public
