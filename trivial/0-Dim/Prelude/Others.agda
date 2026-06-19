open import 0-Dim.Prelude.Agda
open import 0-Dim.Prelude.Tilda

module 0-Dim.Prelude.Others where

-- summ of types
data _[+]_ ([1] [2] : [Any]) : [Any] where
  ↑₁ : [1] → [1] [+] [2]
  ↑₂ : [2] → [1] [+] [2]

module + where
  module _ {[1] [2] : [Any]} where
    symm : [2] [+] [1] → [1] [+] [2]
    symm (↑₁ a) = ↑₂ a
    symm (↑₂ a) = ↑₁ a

-- adjoint pair of morphisms
module _ {O : [Any]} (R : [2~] O → [Any]) (2o @(a ~ b) : [2~] O) where
  record [⊣] : [Any] where
    constructor _⊣_
    field Left : R (a ~ b)
    field Right : R (b ~ a)
  open [⊣] public

module ⊣ where
  module _ {O : [Any]} (R : [2~] O → [Any]) (2o @(a ~ b) : [2~] O) where
    symm : ([⊣] R) (b ~ a) → [⊣] R (a ~ b)
    symm (l ⊣ r) = (r ⊣ l)
