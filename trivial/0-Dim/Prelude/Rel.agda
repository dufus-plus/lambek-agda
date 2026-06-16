open import 0-Dim.Prelude.Agda
open import 0-Dim.Prelude.Tilda
open import 0-Dim.Prelude.Cross

module 0-Dim.Prelude.Rel where

-- the unit relation
data [≡] (Arg : [Any]) : (2arg : [2~] Arg) → [Any] where
  ≡ : (arg : Arg) → [≡] Arg (arg ~ arg)

module ≡ where

  module _ {Arg : [Any]}
           {arg : [1~] Arg} where
    refl : [≡] Arg (arg ~ arg)
    refl = (≡ _)

  module _ {Arg : [Any]}
           {2arg @(a1 ~ a2) : [2~] Arg} where
    symm : [≡] Arg (a2 ~ a1) → [≡] Arg (a1 ~ a2)
    symm (≡ _) = (≡ _)

  module _ {Arg : [Any]}
           {3arg @(a1 ~ a2 ~ a3) : [3~] Arg} where
    tran : [≡] Arg (a1 ~ a2) [×] [≡] Arg (a2 ~ a3) → [≡] Arg (a1 ~ a3)
    tran (≡ _ × ≡ _) = (≡ _)

  module _ {AB @(A > B) : [2~] [Any]}
           (f : A → B)
           {2a @(a1 ~ a2) : [2~] A} where
    cong : [≡] A (a1 ~ a2) → [≡] B (f a1 ~ f a2)
    cong (≡ _) = (≡ _)

-- composition of relations
module _ {[-] [+] : [Any]} {[0] : [Any]} where
  module _ ([₋~₀] : ([-] [~] [0]) → [Any]) ([₀~₊] : ([0] [~] [+]) → [Any])
           (2a @(a- ~ a+): [-] [~] [+]) where
    record _[∙]_ : [Any] where
      constructor _∙_
      field {₀} : [0]
      field ₋~₀ : [₋~₀] (a- ~ ₀)
      field ₀~₊ : [₀~₊] (₀ ~ a+)
    open _[∙]_ public

-- path relation of the given one
module _ (A : [Any]) (R : [2~] A → [Any]) where
  [Path] : (Nat : [Nat]) → ([2~] A → [Any])
  [Path] Zero! = [≡] A
  [Path] (Succ! n) = R [∙] [Path] n

-- inverse relation
module _ {AB @(A ~ B) : [2~] [Any]} (Rba : (B [~] A) → [Any]) where
  [-] : (ab : A [~] B) → [Any]
  [-] (a ~ b) = Rba (b ~ a)
