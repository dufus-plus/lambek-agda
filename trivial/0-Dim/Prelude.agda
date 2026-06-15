import Agda.Primitive
import Agda.Builtin.Nat

--
-- [Any]-theoretical definitions
--
module 0-Dim.Prelude where

open Agda.Primitive public
  using ()
  renaming (Set to [Any])

open Agda.Builtin.Nat public
  using ()
  renaming (Nat to [Nat]; zero to Zero!; suc to Succ!)

private module Test-Any where
  -- ensure `type-in-type` option
  _ : [Any]
  _ = [Any]

record [!] : [Any] where
  constructor !

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

-- yet another pair with named constructor
-- 1st argument is considered as contravariant
record _[~]_ ([-] [+] : [Any]) : [Any] where
  constructor _~_
  field ₋ : [-]
  field ₊ : [+]
open _[~]_ public

infixr 5 _[~]_ _~_
pattern _>_ a b = _~_ a b

[1~]_ : [Any] → [Any]
[2~]_ : [Any] → [Any]
[3~]_ : [Any] → [Any]
[4~]_ : [Any] → [Any]
[1~] A = A
[2~] A = A [~] ([1~] A)
[3~] A = A [~] ([2~] A)
[4~] A = A [~] ([3~] A)

[22~]_ : [Any] → [Any]
[22~] A = [2~] [2~] A
[23~]_ : [Any] → [Any]
[23~] A = [2~] [3~] A
[32~]_ : [Any] → [Any]
[32~] A = [3~] [2~] A
[33~]_ : [Any] → [Any]
[33~] A = [3~] [3~] A

1~_ : {A : [Any]} → A → [1~] A
2~_ : {A : [Any]} → A → [2~] A
3~_ : {A : [Any]} → A → [3~] A
4~_ : {A : [Any]} → A → [4~] A
1~ a = a
2~ a = a ~ (1~ a)
3~ a = a ~ (2~ a)
4~ a = a ~ (3~ a)

[Dup1] : [1~] [Any] → [Any]
[Dup2] : [2~] [Any] → [Any]
[Dup3] : [3~] [Any] → [Any]
[Dup4] : [4~] [Any] → [Any]
[Dup1] A = A
[Dup2] (A ~ B) = A [~] [Dup1] B
[Dup3] (A ~ B) = A [~] [Dup2] B
[Dup4] (A ~ B) = A [~] [Dup3] B

[swap] : [2~] [Any] → [2~] [Any]
[swap] (A ~ B) = B ~ A


swap : {2A : [2~] [Any]} → [Dup2] 2A → [Dup2] ([swap] 2A)
swap (a ~ b) = b ~ a

-- dependent [×]
record _[×d]_ (A : [Any]) (B : A → [Any]) : [Any] where
  constructor _×d_
  field ₁ : A
  field ₂ : B ₁
open _[×d]_ public

infixr 4 _[×d]_ _×d_

-- dependent [~]
record _[~d]_ (A : [Any]) (B : A → [Any]) : [Any] where
  constructor _~d_
  field ₁ : A
  field ₂ : B ₁
open _[~d]_ public

infixr 4 _[~d]_ _~d_

data [≡] (Arg : [Any]) : (2arg : [2~] Arg) → [Any] where
  ≡ : (arg : Arg) → [≡] Arg (arg ~ arg)

module ≡ where
  module _ {Arg : [Any]}
           {3arg @(a1 ~ a2 ~ a3) : [3~] Arg} where
    tran : [≡] Arg (a1 ~ a2) [×] [≡] Arg (a2 ~ a3) → [≡] Arg (a1 ~ a3)
    tran (≡ _ × ≡ _) = (≡ _)
  module _ {AB @(A > B) : [2~] [Any]}
           (f : A → B)
           {2a @(a1 ~ a2) : [2~] A} where
    cong : [≡] A (a1 ~ a2) → [≡] B (f a1 ~ f a2)
    cong (≡ _) = (≡ _)

module _ {[X] : [Any]} where
  ⑴ : [X] → [X]
  ⑴ x = x

module _ {[1] [2] [3] : [Any]} where
  _∘_ : ([1] → [2]) → ([2] → [3]) → ([1] → [3])
  (f₁₂ ∘ f₂₃) a₁ = f₂₃ (f₁₂ a₁)

module _ {[-] [+] : [Any]} {[0] : [Any]} where
  module _ ([₋~₀] : ([-] [~] [0]) → [Any]) ([₀~₊] : ([0] [~] [+]) → [Any])
           (2a @(a- ~ a+): [-] [~] [+]) where
    record _[∙]_ : [Any] where
      constructor _∙_
      field {₀} : [0]
      field ₋~₀ : [₋~₀] (a- ~ ₀)
      field ₀~₊ : [₀~₊] (₀ ~ a+)
    open _[∙]_ public

module _ (A : [Any]) (R : [2~] A → [Any]) where
  [Path] : (Nat : [Nat]) → ([2~] A → [Any])
  [Path] Zero! = [≡] A
  [Path] (Succ! n) = R [∙] [Path] n

module _ {BA @(B ~ A) : [2~] [Any]} (Rba : (B [~] A) → [Any]) (ab @(a ~ b) : A [~] B) where
  record [-] : [Any] where
    constructor -_
    field ₒₚ : Rba (b ~ a)
  open [-] public

data [⊥] : [Any] where

data _[+]_ ([1] [2] : [Any]) : [Any] where
  ↑₁ : [1] → [1] [+] [2]
  ↑₂ : [2] → [1] [+] [2]

-- adjoint pair of morphisms
-- adjoint pair of morphisms
module _ {O : [Any]} (R : O [~] O → [Any]) (2o @(a ~ b) : [2~] O) where
  record [⊣] : [Any] where
    constructor _⊣_
    field $L : R (a ~ b)
    field $R : R (b ~ a)
  open [⊣] public
