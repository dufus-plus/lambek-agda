module 2-Dim.PoCat|PoCat.!quali where

-- re-export qualified
module DblCat where
  open import 2-Dim.PoCat|PoCat.Def-Types public

-- re-export unqualified
open DblCat public using (‼)
