module 2-Dim.DaggPoCat|Cat.!quali where

-- re-export qualified
module DaggPoCat|Cat where
  open import 2-Dim.DaggPoCat|Cat.Def-Types public

-- re-export unqualified
open DaggPoCat|Cat public using (‼)
