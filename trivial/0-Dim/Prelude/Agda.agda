module 0-Dim.Prelude.Agda where

open import Agda.Primitive public
  using ()
  renaming (Set to [Any])

open import Agda.Builtin.Nat public
  using ()
  renaming (Nat to [Nat]; zero to Zero!; suc to Succ!)

private module Test-Any where
  -- ensure `type-in-type` option
  _ : [Any]
  _ = [Any]
