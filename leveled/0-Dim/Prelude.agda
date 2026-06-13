import Agda.Primitive
import Agda.Builtin.Nat

--
-- [Any]-theoretical definitions
--
module 0-Dim.Prelude where

open Agda.Primitive public
  using ()
  renaming
  ( Set to [Typ];
    Setω to [Typ:ω];
    Level to [%Typ];
    lzero to 0%;
    lsuc to 1%+_;
    _⊔_ to _⊔_ )

open Agda.Builtin.Nat public
  using ()
  renaming (Nat to [Nat]; zero to 0!; suc to 1!+)

module _ ℓ where
  [Typ:] : [Typ] (1%+ ℓ)
  [Typ:] = [Typ] ℓ

record [up] ℓ {%a} (A : [Typ:] %a) : [Typ:] (%a ⊔ ℓ) where
  constructor up!
  field dn : A
open [up] public

module _ {%b} where
  record _[^]_ %a (B : [Typ:] %b) : [Typ:] (1%+ %a ⊔ %b) where
    constructor _^_
    field [%] : [Typ:] %a
    field  %: : [%] → B
  open _[^]_ public

[#Typ] = 0% [^] [%Typ]

[Typ*] : [#Typ] → [Typ:ω]
[Typ*] ([%A] ^ A%) = (%a : [%A]) → [Typ:] (A% %a)

1+# : (#A : [#Typ]) → [#Typ]
1+# ([%A] ^ A%) = [%A] ^ λ %a → 1%+ (A% %a)

record [!] : [Typ] where
  constructor !

record [!:] ℓ : [Typ:] ℓ where
  constructor !

module _ {%a %b} where
  record _[×]_ (A : [Typ:] %a) (B : [Typ:] %b) : [Typ:] (%a ⊔ %b) where
    constructor _×_
    field ₁ : A
    field ₂ : B
  open _[×]_ public

  infixr 4 _[×]_ _×_

  pattern _+_ a b = _×_ a b
  pattern _,_ a b = _×_ a b

_#×#_ : (#A #B : [#Typ]) → [#Typ]
([%A] ^ A%) #×# ([%B] ^ B%) = ([%A] [×] [%B]) ^ λ (%a × %b) → A% %a ⊔ B% %b

module _ {#A} {#B} where
  _*[×]*_ : [Typ*] #A → [Typ*] #B → [Typ*] (#A #×# #B)
  (A: *[×]* B:) (%a × %b) = A: %a [×] B: %b

module _ {%a} where
  [2×]_ : [Typ:] %a → [Typ:] %a
  [2×]_ A = A [×] A
  2× : {A : [Typ:] %a} → A → [2×] A
  2× a = a × a

[2×]#_ : [#Typ] → [#Typ]
[2×]# #A = #A #×# #A

module _ {#A@([%A] ^ A%) : 0% [^] [%Typ]} where
  [2×]*_ : (A: : [Typ*] #A) → [Typ*] ([2×]# #A)
  [2×]* A: = A: *[×]* A:

module _ {%a %b} where
  record _[~]_ (A : [Typ:] %a) (B : [Typ:] %b) : [Typ:] (%a ⊔ %b) where
    constructor _~_
    field ₋ : A
    field ₊ : B
  open _[~]_ public

  infixr 5 _[~]_ _~_
  pattern _>_ a b = _~_ a b

record _[ω~ω]_ (A : [Typ:ω]) (B : [Typ:ω]) : [Typ:ω] where
  constructor _~_
  field ₋ : A
  field ₊ : B
open _[ω~ω]_ public

_#~#_ : (#A #B : [#Typ]) → [#Typ]
([%A] ^ A%) #~# ([%B] ^ B%) = ([%A] [~] [%B]) ^ λ (%a ~ %b) → A% %a ⊔ B% %b

module _ {#A} {#B} where
  _:[~]:_ : [Typ*] #A → [Typ*] #B → [Typ*] (#A #~# #B)
  (A: :[~]: B:) (%a ~ %b) = A: %a [~] B: %b

module _ {%a %b} {[#A] : [Typ:] %a} {[#B] : [Typ:] %b} where
  _*[~]*_ : ([#A] → [Typ:ω]) → ([#B] → [Typ:ω]) → ([#A] [~] [#B]) → [Typ:ω]
  (A* *[~]* B*) (#A ~ #B) = A* #A [ω~ω] B* #B

module _ {%a} where
  [1~]_ : [Typ:] %a → [Typ:] %a
  [2~]_ : [Typ:] %a → [Typ:] %a
  [3~]_ : [Typ:] %a → [Typ:] %a
  [4~]_ : [Typ:] %a → [Typ:] %a
  [1~] A = A
  [2~] A = A [~] ([1~] A)
  [3~] A = A [~] ([2~] A)
  [4~] A = A [~] ([3~] A)

module _ {%a} {A : [Typ:] %a} where
  1~_ : A → [1~] A
  2~_ : A → [2~] A
  3~_ : A → [3~] A
  4~_ : A → [4~] A
  1~ a = a
  2~ a = a ~ (1~ a)
  3~ a = a ~ (2~ a)
  4~ a = a ~ (3~ a)

1⊔%_ : [1~] [%Typ] → [%Typ]
2⊔%_ : [2~] [%Typ] → [%Typ]
3⊔%_ : [3~] [%Typ] → [%Typ]
4⊔%_ : [4~] [%Typ] → [%Typ]
1⊔% %a = %a
2⊔% (%a ~ %b) = %a ⊔ (1⊔% %b)
3⊔% (%a ~ %b) = %a ⊔ (2⊔% %b)
4⊔% (%a ~ %b) = %a ⊔ (3⊔% %b)

[1~]#_ : [#Typ] → [#Typ]
[2~]#_ : [#Typ] → [#Typ]
[3~]#_ : [#Typ] → [#Typ]
[4~]#_ : [#Typ] → [#Typ]
[1~]# #A = #A
[2~]# #A = #A #~# ([1~]# #A)
[3~]# #A = #A #~# ([2~]# #A)
[4~]# #A = #A #~# ([3~]# #A)

[22~]#_ : [#Typ] → [#Typ]
[23~]#_ : [#Typ] → [#Typ]
[32~]#_ : [#Typ] → [#Typ]
[33~]#_ : [#Typ] → [#Typ]
[22~]# #A = [2~]# [2~]# #A
[23~]# #A = [2~]# [3~]# #A
[32~]# #A = [3~]# [2~]# #A
[33~]# #A = [3~]# [3~]# #A

module _ {#A} where
  [1~]:_ : [Typ*] #A → [Typ*] ([1~]# #A)
  [2~]:_ : [Typ*] #A → [Typ*] ([2~]# #A)
  [3~]:_ : [Typ*] #A → [Typ*] ([3~]# #A)
  [4~]:_ : [Typ*] #A → [Typ*] ([4~]# #A)
  [1~]: A: = A:
  [2~]: A: = A: :[~]: ([1~]: A:)
  [3~]: A: = A: :[~]: ([2~]: A:)
  [4~]: A: = A: :[~]: ([3~]: A:)

module _ {%a} {[#A] : [Typ:] %a} where
  [1~]*_ : ([#A] → [Typ:ω]) → ([1~] [#A]) → [Typ:ω]
  [2~]*_ : ([#A] → [Typ:ω]) → ([2~] [#A]) → [Typ:ω]
  [3~]*_ : ([#A] → [Typ:ω]) → ([3~] [#A]) → [Typ:ω]
  [4~]*_ : ([#A] → [Typ:ω]) → ([4~] [#A]) → [Typ:ω]
  [1~]* A* = A*
  [2~]* A* = A* *[~]* ([1~]* A*)
  [3~]* A* = A* *[~]* ([2~]* A*)
  [4~]* A* = A* *[~]* ([3~]* A*)

module _ {#A} where
  [22~]:_ : [Typ*] #A → [Typ*] ([22~]# #A)
  [23~]:_ : [Typ*] #A → [Typ*] ([23~]# #A)
  [32~]:_ : [Typ*] #A → [Typ*] ([32~]# #A)
  [33~]:_ : [Typ*] #A → [Typ*] ([33~]# #A)
  [22~]: A: = [2~]: [2~]: A:
  [23~]: A: = [2~]: [3~]: A:
  [32~]: A: = [3~]: [2~]: A:
  [33~]: A: = [3~]: [3~]: A:

module _ {%1a} where
  [Dup1] : ([1~]: [Typ:]) %1a → [Typ:] (1⊔% %1a)
  [Dup1] A = A

module _ {%2a} where
  [Dup2] : ([2~]: [Typ:]) %2a → [Typ:] (2⊔% %2a)
  [Dup2] (A ~ B) = A [~] [Dup1] B

module _ {%3a} where
  [Dup3] : ([3~]: [Typ:]) %3a → [Typ:] (3⊔% %3a)
  [Dup3] (A ~ B) = A [~] [Dup2] B

module _ {%4a} where
  [Dup4] : ([4~]: [Typ:]) %4a → [Typ:] (4⊔% %4a)
  [Dup4] (A ~ B) = A [~] [Dup3] B

swap% : [2~] [%Typ] → [2~] [%Typ]
swap% (%a ~ %b) = (%b ~ %a)

module _ {%2a} where
  [swap] : ([2~]: [Typ:]) %2a → ([2~]: [Typ:]) (swap% %2a)
  [swap] (A ~ B) = B ~ A

  swap : {2A : ([2~]: [Typ:]) %2a} → [Dup2] 2A → [Dup2] ([swap] 2A)
  swap (a ~ b) = b ~ a

-- Dependent [×]
module _ {%a %b} where
  record _[d×]_ (A : [Typ:] %a) (B : A → [Typ:] %b) : [Typ:] (%a ⊔ %b) where
    constructor _d×_
    field ₁ : A
    field ₂ : B ₁
  open _[d×]_ public

-- Dependent [~]
module _ {%a %b} where
  record _[d~]_ (A : [Typ:] %a) (B : A → [Typ:] %b) : [Typ:] (%a ⊔ %b) where
    constructor _d~_
    field ₋ : A
    field ₊ : B ₋
  open _[d~]_ public

module _ {%arg} (Arg : [Typ:] %arg) where
  data [≡] : (2arg : [2~] Arg) → [Typ:] (%arg) where
    ≡ : (arg : Arg) → [≡] (arg ~ arg)

  module ≡ (3arg @(a1 ~ a2 ~ a3) : [3~] Arg) where
    tran : [≡] (a1 ~ a2) [×] [≡] (a2 ~ a3) → [≡] (a1 ~ a3)
    tran (≡ _ × ≡ _) = (≡ _)

module _ ℓ {%arg} (Arg : [Typ:] %arg) where
  data [≡:] : (2arg : [2~] Arg) → [Typ:] (ℓ ⊔ %arg) where
    ≡: : (arg : Arg) → [≡:] (arg ~ arg)

  module ≡: (3arg @(a1 ~ a2 ~ a3) : [3~] Arg) where
    tran : [≡:] (a1 ~ a2) [×] [≡:] (a2 ~ a3) → [≡:] (a1 ~ a3)
    tran (≡: _ × ≡: _) = (≡: _)

module _ {%x} {[X] : [Typ:] %x} where
  ⑴ : [X] → [X]
  ⑴ x = x

module _ {%1 %2 %3} {[1] : [Typ:] %1} {[2] : [Typ:] %2} {[3] : [Typ:] %3} where
  _∘_ : ([1] → [2]) → ([2] → [3]) → ([1] → [3])
  (f₁₂ ∘ f₂₃) a₁ = f₂₃ (f₁₂ a₁)

module _ {%- %+ %0 %-0 %0+}
         {[-] : [Typ:] %- } {[+] : [Typ:] %+} {[0] : [Typ:] %0} where
  module _ ([₋~₀] : ([-] [~] [0]) → [Typ:] %-0)
           ([₀~₊] : ([0] [~] [+]) → [Typ:] %0+)
           (2a @(a- ~ a+): [-] [~] [+]) where
    record _[∙]_ : [Typ:] (%0 ⊔ %-0 ⊔ %0+) where
      constructor _∙_
      field {₀} : [0]
      field ₋~₀ : [₋~₀] (a- ~ ₀)
      field ₀~₊ : [₀~₊] (₀ ~ a+)
    open _[∙]_ public

module _ {%a} (A : [Typ:] %a) where
  [Vect] : (Nat : [Nat]) → [Typ:] %a
  [Vect] 0! = [!:] %a
  [Vect] (1!+ n) = A [×] [Vect] n

module _ {%a %r} (A : [Typ:] %a) (R : [2~] A → [Typ:] %r) where
  [Path] : (Nat : [Nat]) → ([2~] A → [Typ:] (%r ⊔ %a))
  [Path] 0! = [≡:] %r A
  [Path] (1!+ n) = R [∙] [Path] n

module _ {%ba %r}
         {BA @(B ~ A) : ([2~]: [Typ:]) %ba}
         (Rba : (B [~] A) → [Typ:] %r)
         (ab @(a ~ b) : A [~] B) where
  record [-] : [Typ] %r where
    constructor -_
    field ₒₚ : Rba (b ~ a)
  open [-] public

data [⊥] : [Typ] where

data [⊥:] ℓ : [Typ:] ℓ where

module _ {%1 %2} where
  data _[+]_ ([1] : [Typ:] %1) ([2] : [Typ:] %2) : [Typ:] (%1 ⊔ %2) where
    ↑₁ : [1] → [1] [+] [2]
    ↑₂ : [2] → [1] [+] [2]

module _ {%o %r} {O : [Typ:] %o}
    (R : O [~] O → [Typ:] %r)
    (2o @(a ~ b) : [2~] O) where
  record [⊣] : [Typ:] %r where
    constructor _⊣_
    field $L : R (a ~ b)
    field $R : R (b ~ a)
  open [⊣] public

module _ {%i %j}
    (I : [Typ:] %i) (J : [Typ:] %j) where
  record _[/]_ : [Typ:] (%i ⊔ %j) where
    constructor _/_
    field i : I
    field j : J
  open _[/]_ public
