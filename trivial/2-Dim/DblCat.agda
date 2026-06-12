open import 0-Dim

module 2-Dim.DblCat where

-- re-export qualified
module DblCat where
  open import 2-Dim.DblCat.Defs public

-- re-export unqualified
open DblCat public
  using (‼; [DblCat]; module [DblCat])
open [DblCat] public
