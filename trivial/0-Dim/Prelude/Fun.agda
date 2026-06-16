open import 0-Dim.Prelude.Agda

module 0-Dim.Prelude.Fun where

module _ {[X] : [Any]} where
  ⑴ : [X] → [X]
  ⑴ x = x

module _ {[1] [2] [3] : [Any]} where
  _∘_ : ([1] → [2]) → ([2] → [3]) → ([1] → [3])
  (f₁₂ ∘ f₂₃) a₁ = f₂₃ (f₁₂ a₁)
