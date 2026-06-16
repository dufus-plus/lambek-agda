--
-- (P)artially (o)rdered (Set)oid
--

-- packaging the modules
module 1-Dim.PoSet.!publi where

-- base package
open import 1-Dim.PoSet.!quali public

-- re-export the constructors & fields of records
open PoSet using (↑; ‼) public
open import 1-Dim.PoSet.Def-Types-pub public
