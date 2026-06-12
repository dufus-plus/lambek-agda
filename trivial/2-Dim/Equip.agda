open import 0-Dim

module 2-Struct.Cat where

-- re-export qualified
module Cat where
  open 2-Dim.Cat.Defs public

-- re-export unqualified
open Cat using ([Cat]; module [Cat])
open [Cat] public
