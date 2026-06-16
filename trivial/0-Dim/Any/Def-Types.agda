open import 0-Dim.Prelude.!all

--
-- type definitions for 0-equipment [Any]
--
module 0-Dim.Any.Def-Types where

-- use Agda universe type `Set` renamed to `[Any]`
-- in Prelude because of `type-in-type` option
[Ob] : [Any]
[Ob] = [Any]

[Fun] : [2~] [Ob] → [Any]
[Fun] (A > B) = A → B

[0-Fun] : [!] [~] [Ob] → [Any]
[0-Fun] (_ > B) = B

[2-Fun] : ([2×] [Ob]) [~] [Ob] → [Any]
[2-Fun] ((A1 × A2) > B) = (2a : A1 [×] A2) → B

[Rel] : [2~] [Ob] → [Any]
[Rel] (A ~ B) = A [~] B → [Any]

module _ (AB @(A > B): [2~] [Ob])
         (2f @(f1 > f2) : [2~] [Fun] AB) where
  Fun-[Id] : [Any]
  Fun-[Id] = (a : A) → [≡] B (f1 a ~ f2 a)

module _ (AB : [2~] [Ob])
         (2R @(R1 > R2) : [2~] [Rel] AB) where
  Rel-[Fun] : [Any]
  Rel-[Fun] = (ab : [Dup2] AB) → [Fun] (R1 ab > R2 ab)

module _ (A : [Ob])
         (2R @(U1 > R2) : [!] [~] [Rel] (2~ A)) where
  Rel-[0-Fun] : [Any]
  Rel-[0-Fun] = (a : A) → R2 (2~ a)

module _ (2A @(A ~ B) : [2~] [Ob])
         (2R @(R1 > R2) : [-] [Rel] 2A [~] [Rel] 2A) where
  Rel-[S-Fun] : [Any]
  Rel-[S-Fun] = (2a : [Dup2] 2A) → [Fun] ([-] R1 2a > R2 2a)

module _ (3A @(A ~ B ~ C) : [3~] [Ob])
         (2R @((R11 × R12) > R2) : ([Rel] (A ~ B) [×] [Rel] (B ~ C)) [~] [Rel] (A ~ C)) where
  Rel-[2-Fun] : [Any]
  Rel-[2-Fun] = (3a @(a ~ b ~ c) : [Dup3] 3A) → [2-Fun] ((R11 (a ~ b) × R12 (b ~ c)) > R2 (a ~ c))

module _ (AB : [2~] [Ob])
         (2R @(R1 ~ R2) : [2~] [Rel] AB) where
  Rel-[Rel] : [Any]
  Rel-[Rel] = (ab : [Dup2] AB) → [Rel] (R1 ab ~ R2 ab)

module _ (A : [Ob])
         (2R @(U1 ~ R2) : [!] [~] [Rel] (2~ A)) where
  Rel-[0-Rel] : [Any]
  Rel-[0-Rel] = (a : A) → [Rel] ([!] ~ R2 (2~ a))

module _ (3A @(A ~ B ~ C) : [3~] [Ob])
         (2R @((R11 × R12) > R2) : ([Rel] (A ~ B) [×] [Rel] (B ~ C)) [~] [Rel] (A ~ C)) where
  Rel-[2-Rel] : [Any]
  Rel-[2-Rel] = (3a @(a ~ b ~ c): [Dup3] 3A) → [Rel] ((R11 (a ~ b) [×] R12 (b ~ c)) > R2 (a ~ c))

[Dup|Dup] : [22~] [Ob] → [Any]
[Dup|Dup] (2X1 ~ 2X2) = [Dup2] 2X1 [~] [Dup2] 2X2

[DD-flip] : [22~] [Ob] → [22~] [Ob]
[DD-flip] ((X11 ~ X12) ~ (X21 ~ X22)) = ((X11 ~ X21) ~ (X12 ~ X22))
DD-flip : {22X : [22~] [Ob]} → [Dup|Dup] 22X → [Dup|Dup] ([DD-flip] 22X)
DD-flip ((x11 ~ x12) ~ (x21 ~ x22)) = ((x11 ~ x21) ~ (x12 ~ x22))

[2|2~] : [2~] [Ob] → [22~] [Ob]
[2|2~] (A1 ~ A2) = (A1 ~ A2) ~ (A1 ~ A2)
[2~|2] : [2~] [Ob] → [22~] [Ob]
[2~|2] (A1 ~ A2) = (A1 ~ A1) ~ (A2 ~ A2)

2|2~ : {2A : [2~] [Ob]} → [Dup2] 2A → [Dup|Dup] ([2|2~] 2A)
2|2~ (a1 ~ a2) = (a1 ~ a2) ~ (a1 ~ a2)
2~|2 : {2A : [2~] [Ob]} → [Dup2] 2A → [Dup|Dup] ([2~|2] 2A)
2~|2 (a1 ~ a2) = (a1 ~ a1) ~ (a2 ~ a2)

[Dup|≡] : {2A : [2~] [Ob]} → [Dup|Dup] ([2|2~] 2A) → [Any]
[Dup|≡] ((x11 ~ x12) ~ (x21 ~ x22)) = [≡] _ (x11 ~ x21) [~] [≡] _ (x12 ~ x22)
[≡|Dup] : {2A : [2~] [Ob]} → [Dup|Dup] ([2~|2] 2A) → [Any]
[≡|Dup] ((x11 ~ x12) ~ (x21 ~ x22)) = [≡] _ (x11 ~ x12) [~] [≡] _ (x21 ~ x22)

[Dup|Fun] : [22~] [Ob] → [Any]
[Dup|Fun] ((X11 ~ X12) ~ (X21 ~ X22)) = [Fun] (X11 ~ X21) [~] [Fun] (X12 ~ X22)
[Fun|Dup] : [22~] [Ob] → [Any]
[Fun|Dup] ((X11 ~ X12) ~ (X21 ~ X22)) = [Fun] (X11 ~ X12) [~] [Fun] (X21 ~ X22)
[Dup|0Fun] : ([Ob] [~] ([2~] [Ob])) → [Any]
[Dup|0Fun] ((X1) ~ (X21 ~ X22)) = [Fun] (X1 ~ X21) [~] [Fun] (X1 ~ X22)

[Dup|Rel] : [22~] [Ob] → [Any]
[Dup|Rel] ((X11 ~ X12) ~ (X21 ~ X22)) = [Rel] (X11 ~ X21) [~] [Rel] (X12 ~ X22)
[Rel|Dup] : [22~] [Ob] → [Any]
[Rel|Dup] ((X11 ~ X12) ~ (X21 ~ X22)) = [Rel] (X11 ~ X12) [~] [Rel] (X21 ~ X22)
[Rel|0Dup] : ([Ob] [~] ([2~] [Ob])) → [Any]
[Rel|0Dup] ((X1) ~ (X21 ~ X22)) = [!] [~] [Rel] (X21 ~ X22)

[Dup|R] : {22A : [22~] [Ob]} → (2VR : [Dup|Rel] 22A) → (22a : [Dup|Dup] 22A) → [Any]
[Dup|R] (VR1 ~ VR2) ((a11 ~ a12) ~ (a21 ~ a22)) = VR1 (a11 ~ a21) [~] VR2 (a12 ~ a22)
[R|Dup] : {22A : [22~] [Ob]} → (2HR : [Rel|Dup] 22A) → (22a : [Dup|Dup] 22A) → [Any]
[R|Dup] (HR1 ~ HR2) ((a11 ~ a12) ~ (a21 ~ a22)) = HR1 (a11 ~ a12) [~] HR2 (a21 ~ a22)

[Rel|Fun] : (22X : [22~] [Ob])
        (2VF : [Dup|Fun] 22X)
        (2HR : [Rel|Dup] 22X) → [Any]
[Rel|Fun] (2X1 ~ _) (VF1 ~ VF2) (HR1 ~ HR2) =
  (2x @(x11 ~ x12) : [Dup2] 2X1) →
  (hr1 : HR1 (x11 ~ x12)) → HR2 (VF1 x11 ~ VF2 x12)

[Rel|0Fun] : (22X : [Ob] [~] ([2~] [Ob]))
        (2VF : [Dup|0Fun] 22X)
        (2HR : [Rel|0Dup] 22X) → [Any]
[Rel|0Fun] (X1 ~ _) (VF1 ~ VF2) (! ~ HR2) =
  (x1 : X1) →
  HR2 (VF1 x1 ~ VF2 x1)

_2|2$_ : {22X : [22~] [Ob]} → (2VR : [Dup|Rel] 22X) → ([Dup|Dup] 22X → [Any])
_2|2$_ (VR1 ~ VR2) ((x11 ~ x12) ~ (x21 ~ x22)) = VR1 (x11 ~ x21) [~] VR2 (x12 ~ x22)

_2$|2_ : {22X : [22~] [Ob]} → (2HR : [Rel|Dup] 22X) → ([Dup|Dup] 22X → [Any])
_2$|2_ (HR1 ~ HR2) ((x11 ~ x12) ~ (x21 ~ x22)) = HR1 (x11 ~ x12) [~] HR2 (x21 ~ x22)

[Rel|Rel] :
  (22X : [22~] [Ob])
  (2VR : [Dup|Rel] 22X)
  (2HR : [Rel|Dup] 22X) → [Any]
[Rel|Rel] 22X 2VR 2HR =
  (22x : [Dup|Dup] 22X)
  (2vr : [Dup|R] 2VR 22x)
  (2hr : [R|Dup] 2HR 22x) → [Any]
