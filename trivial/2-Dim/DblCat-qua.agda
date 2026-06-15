module 2-Dim.DblCat-qua where

-- re-export qualified
module DblCat where
  open import 2-Dim.DblCat.Def-Types public

-- re-export unqualified
open DblCat public using (‼)
