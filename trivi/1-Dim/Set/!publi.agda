--
-- define (Set)oids
--

-- packaging the modules
module 1-Dim.Set.!publi where

-- base package:
open import 1-Dim.Set.!quali public

-- re-export un-qualified:
-- constructors and fields of records
open Set using (↑; ‼) public
open import 1-Dim.Set.Def-Types-pub public
