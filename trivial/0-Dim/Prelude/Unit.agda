open import 0-Dim.Prelude.Agda

module 0-Dim.Prelude.Unit where

-- the product-neutral type
record [!] : [Any] where
  constructor !

-- the summ-neutral type
data [⊥] : [Any] where
