open import 0-Dim.Prelude.Agda

module 0-Dim.Prelude.Tilda where

-- yet another pair with named constructor
-- 1st argument is considered as contravariant
record _[~]_ ([-] [+] : [Any]) : [Any] where
  constructor _~_
  field ↓₋ : [-]
  field ↓₊ : [+]
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

[Dup2|Dup2] : [22~] [Any] → [Any]
[Dup2|Dup2] (2A1 ~ 2A2) = [Dup2] 2A1 [~] [Dup2] 2A2

[swap] : [2~] [Any] → [2~] [Any]
[swap] (A ~ B) = B ~ A

swap : {2A : [2~] [Any]} → [Dup2] 2A → [Dup2] ([swap] 2A)
swap (a ~ b) = b ~ a

-- dependent [~]
record _[~d]_ (A : [Any]) (B : A → [Any]) : [Any] where
  constructor _~d_
  field ↓₋ : A
  field ↓₊ : B ↓₋
open _[~d]_ public

infixr 4 _[~d]_ _~d_
