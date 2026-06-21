module 2-Dim.Cat|Cat.!quali where

-- re-export qualified
module Cat|Cat where
  open import 2-Dim.Cat|Cat.Def-Types public

-- re-export unqualified
open Cat|Cat public using (‼)
