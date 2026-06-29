module 2-Dim.PoCat|PoCat.!quali where

-- re-export qualified
module PoCat|PoCat where
  open import 2-Dim.PoCat|PoCat.Def-Types public

-- re-export unqualified
open PoCat|PoCat public using (‼)
