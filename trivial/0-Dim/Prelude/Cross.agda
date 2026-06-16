open import 0-Dim.Prelude.Agda

module 0-Dim.Prelude.Cross where

record _[×]_ (A B : [Any]) : [Any] where
  constructor _×_
  field ₁ : A
  field ₂ : B
open _[×]_ public

infixr 4 _[×]_ _×_

pattern _+_ a b = _×_ a b
pattern _,_ a b = _×_ a b

[2×]_ : [Any] → [Any]
[2×] A = A [×] A
2×_ : {A : [Any]} → A → [2×] A
2× a = a × a

-- dependent [×]
record _[×d]_ (A : [Any]) (B : A → [Any]) : [Any] where
  constructor _×d_
  field ₁ : A
  field ₂ : B ₁
open _[×d]_ public

infixr 4 _[×d]_ _×d_
