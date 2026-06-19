module 0-Dim.Prelude.Agda where

open import Agda.Primitive public
  using ()
  renaming (Set to [Any])

open import Agda.Builtin.Nat public
  using ()
  renaming
    ( Nat to [Nat];
      zero to 0!;
      suc to 1!+ )

module Nat where
  open import Agda.Builtin.Nat public
    using ()
    renaming
      ( _+_ to Summ2;
        _*_ to Prod2 )
  pattern 1! = 1!+ 0!
open Nat using (1!) public

private module Test-Any where
  -- ensure `type-in-type` option
  _ : [Any]
  _ = [Any]
