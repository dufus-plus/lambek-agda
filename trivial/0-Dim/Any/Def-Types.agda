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
[Fun] (A > B) = (a : A) → B

[0-Fun] : [!] [~] [Ob] → [Any]
[0-Fun] (_ > B) = B

[2-Fun] : ([2×] [Ob]) [~] [Ob] → [Any]
[2-Fun] ((A1 × A2) > B) = (2a : A1 [×] A2) → B

[Rel] : [2~] [Ob] → [Any]
[Rel] (A ~ B) = (a~b : A [~] B) → [Any]

[0-Rel] : [!] [~] [Ob] → [Any]
[0-Rel] (_ > B) = (!~b : [!] [~] B) → [Any]

[2-Rel] : ([2×] [Ob]) [~] [Ob] → [Any]
[2-Rel] ((A1 × A2) > B) = (2a~b : (A1 [×] A2) [~] B) → [Any]

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

[DD-flip] : [22~] [Ob] → [22~] [Ob]
[DD-flip] ((X11 ~ X12) ~ (X21 ~ X22)) = ((X11 ~ X21) ~ (X12 ~ X22))
DD-flip : {22X : [22~] [Ob]} → [Dup2|Dup2] 22X → [Dup2|Dup2] ([DD-flip] 22X)
DD-flip ((x11 ~ x12) ~ (x21 ~ x22)) = ((x11 ~ x21) ~ (x12 ~ x22))

[2|2~] : [2~] [Ob] → [22~] [Ob]
[2|2~] (A1 ~ A2) = (A1 ~ A2) ~ (A1 ~ A2)
[2~|2] : [2~] [Ob] → [22~] [Ob]
[2~|2] (A1 ~ A2) = (A1 ~ A1) ~ (A2 ~ A2)

2|2~ : {2A : [2~] [Ob]} → [Dup2] 2A → [Dup2|Dup2] ([2|2~] 2A)
2|2~ (a1 ~ a2) = (a1 ~ a2) ~ (a1 ~ a2)
2~|2 : {2A : [2~] [Ob]} → [Dup2] 2A → [Dup2|Dup2] ([2~|2] 2A)
2~|2 (a1 ~ a2) = (a1 ~ a1) ~ (a2 ~ a2)

[Dup|≡] : {2A : [2~] [Ob]} → [Dup2|Dup2] ([2|2~] 2A) → [Any]
[Dup|≡] ((x11 ~ x12) ~ (x21 ~ x22)) = [≡] _ (x11 ~ x21) [~] [≡] _ (x12 ~ x22)
[≡|Dup] : {2A : [2~] [Ob]} → [Dup2|Dup2] ([2~|2] 2A) → [Any]
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

[Dup3|Rel] : [23~] [Ob] → [Any]
[Dup3|Rel] ((X11 ~ X12 ~ X13) ~ (X21 ~ X22 ~ X23)) =
  [Rel] (X11 ~ X21) [~] [Rel] (X12 ~ X22) [~] [Rel] (X13 ~ X23)
[Rel|Dup3] : [32~] [Ob] → [Any]
[Rel|Dup3] ((X11 ~ X12) ~ (X21 ~ X22) ~ (X31 ~ X32)) =
  [Rel] (X11 ~ X12) [~] [Rel] (X21 ~ X22) [~] [Rel] (X31 ~ X32)

[Rel|0Dup] : ([Ob] [~] ([2~] [Ob])) → [Any]
[Rel|0Dup] ((X1) ~ (X21 ~ X22)) = [!] [~] [Rel] (X21 ~ X22)

[Dup|R] : {22A : [22~] [Ob]} → (2VR : [Dup|Rel] 22A) → (22a : [Dup2|Dup2] 22A) → [Any]
[Dup|R] (VR1 ~ VR2) ((a11 ~ a12) ~ (a21 ~ a22)) = VR1 (a11 ~ a21) [~] VR2 (a12 ~ a22)
[R|Dup] : {22A : [22~] [Ob]} → (2HR : [Rel|Dup] 22A) → (22a : [Dup2|Dup2] 22A) → [Any]
[R|Dup] (HR1 ~ HR2) ((a11 ~ a12) ~ (a21 ~ a22)) = HR1 (a11 ~ a12) [~] HR2 (a21 ~ a22)

[Dup3|R] : {23A : [23~] [Ob]} → (3VR : [Dup3|Rel] 23A) → (23a : [Dup2|Dup3] 23A) → [Any]
[Dup3|R] (VR1 ~ VR2 ~ VR3) ((x11 ~ x12 ~ x13) ~ (x21 ~ x22 ~ x23)) =
  VR1 (x11 ~ x21) [~] VR2 (x12 ~ x22) [~] VR3 (x13 ~ x23)
[R|Dup3] : {32A : [32~] [Ob]} → (3HR : [Rel|Dup3] 32A) → (32a : [Dup3|Dup2] 32A) → [Any]
[R|Dup3] (HR1 ~ HR2 ~ HR3) ((x11 ~ x12) ~ (x21 ~ x22) ~ (x31 ~ x32)) =
  HR1 (x11 ~ x12) [~] HR2 (x21 ~ x22) [~] HR3 (x31 ~ x32)

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

_2|2$_ : {22X : [22~] [Ob]} → (2VR : [Dup|Rel] 22X) → ([Dup2|Dup2] 22X → [Any])
_2|2$_ (VR1 ~ VR2) ((x11 ~ x12) ~ (x21 ~ x22)) = VR1 (x11 ~ x21) [~] VR2 (x12 ~ x22)

_2$|2_ : {22X : [22~] [Ob]} → (2HR : [Rel|Dup] 22X) → ([Dup2|Dup2] 22X → [Any])
_2$|2_ (HR1 ~ HR2) ((x11 ~ x12) ~ (x21 ~ x22)) = HR1 (x11 ~ x12) [~] HR2 (x21 ~ x22)

[Rel|Rel] :
  (22X : [22~] [Ob])
  (2VR : [Dup|Rel] 22X)
  (2HR : [Rel|Dup] 22X) → [Any]
[Rel|Rel] 22X 2VR 2HR =
  (22x : [Dup2|Dup2] 22X)
  (2vr : [Dup|R] 2VR 22x)
  (2hr : [R|Dup] 2HR 22x) → [Any]

Rel|Rel-[Fun] :
  (22X : [22~] [Ob])
  (2VR : [Dup|Rel] 22X)
  (2HR : [Rel|Dup] 22X)
  (2HV @(HV1 ~ HV2) : [2~] [Rel|Rel] 22X 2VR 2HR) → [Any]
Rel|Rel-[Fun] 22X 2VR 2HR (HV1 ~ HV2) =
  (22x : [Dup2|Dup2] 22X)
  (2vr : [Dup|R] 2VR 22x)
  (2hr : [R|Dup] 2HR 22x)
  (hv1 : HV1 22x 2vr 2hr) → HV2 22x 2vr 2hr

Rel-[Dup|0-Fun] : (2X : [2~] [Ob]) (2VR : [Dup|Rel] (2|2~ 2X)) → [Any]
Rel-[Dup|0-Fun] (X1 ~ X2) (VR1 ~ VR2) =
  Rel-[0-Fun] X1 (! ~ VR1) [~] Rel-[0-Fun] X2 (! ~ VR2)
Rel-[0-Fun|Dup] : (2X : [2~] [Ob]) (2HR : [Rel|Dup] (2~|2 2X)) → [Any]
Rel-[0-Fun|Dup] (X1 ~ X2) (HR1 ~ HR2) =
  Rel-[0-Fun] X1 (! ~ HR1) [~] Rel-[0-Fun] X2 (! ~ HR2)

Rel|Rel-[0₁-Fun] :
  (2X : [2~] [Ob]) (let 22X = 2~|2 2X)
  (VR : [Rel] 2X) (let 2VR = 2~ VR)
  (2HR : [Rel|Dup] 22X)
  (!H|V : [!] [~] [Rel|Rel] 22X 2VR 2HR)
  (2HId : Rel-[0-Fun|Dup] 2X 2HR) → [Any]
Rel|Rel-[0₁-Fun] 2X VR 2HR (! ~ H|V) (HId1 ~ HId2) =
  (2x @(x1 ~ x2): [Dup2] 2X) (let 22x = 2~|2 2x)
  (vr : VR 2x) (let 2vr = 2~ vr) →
  H|V 22x 2vr (HId1 x1 ~ HId2 x2)

Rel|Rel-[0₂-Fun] :
  (2X : [2~] [Ob]) (let 22X = 2|2~ 2X)
  (2VR : [Dup|Rel] 22X)
  (HR : [Rel] 2X) (let 2HR = 2~ HR)
  (H|V : [!] [~] [Rel|Rel] 22X 2VR 2HR)
  (2VId : Rel-[Dup|0-Fun] 2X 2VR) → [Any]
Rel|Rel-[0₂-Fun] 2X 2VR HR (! ~ H|V) (VId1 ~ VId2) =
  (2x @(x1 ~ x2): [Dup2] 2X) (let 22x = 2|2~ 2x)
  (hr : HR 2x) (let 2hr = 2~ hr) →
  H|V 22x (VId1 x1 ~ VId2 x2) 2hr

Rel|Rel-[2₁-Fun] :
  (23X @((X11 ~ X12 ~ X13) ~ (X21 ~ X22 ~ X23)): [23~] [Ob])
  (3VR @(VR1 ~ VR2 ~ VR3): [Dup3|Rel] 23X)
  (23HR @(((HR11 × HR12) ~ HR1R) ~ ((HR21 × HR22) ~ HR2R)) :
          (([Rel] (X11 ~ X12) [×] [Rel] (X12 ~ X13)) [~] [Rel] (X11 ~ X13)) [~]
          (([Rel] (X21 ~ X22) [×] [Rel] (X22 ~ X23)) [~] [Rel] (X21 ~ X23)) )
  (3HV : ([Rel|Rel] _ (VR1 ~ VR2) (HR11 ~ HR21) [×]
          [Rel|Rel] _ (VR2 ~ VR3) (HR12 ~ HR22)) [~]
          [Rel|Rel] _ (VR1 ~ VR3) (HR1R ~ HR2R))
  (2HMu : Rel-[2-Fun] _ ((HR11 × HR12) ~ HR1R) [~] Rel-[2-Fun] _ ((HR21 × HR22) ~ HR2R))
  → [Any]
Rel|Rel-[2₁-Fun] 23X 3VR
  (((HR11 × HR12) ~ HR1R) ~ ((HR21 × HR22) ~ HR2R))
  ((HV1 × HV2) ~ HVR) (HMu1 ~ HMu2)
  =
  (23x @((x11 ~ x12 ~ x13) ~ (x21 ~ x22 ~ x23)) : [Dup2|Dup3] 23X) →
  (3vr @(vr1 ~ vr2 ~ vr3) : [Dup3|R] 3VR 23x)
  (22hr @((hr11 × hr12) ~ (hr21 × hr22)) :
          (HR11 (x11 ~ x12) [×] HR12 (x12 ~ x13)) [~]
          (HR21 (x21 ~ x22) [×] HR22 (x22 ~ x23)))
  (2hv : HV1 _ (vr1 ~ vr2) (hr11 ~ hr21) [×]
         HV2 _ (vr2 ~ vr3) (hr12 ~ hr22)) →
         HVR _ (vr1 ~ vr3) (HMu1 _ (hr11 × hr12) ~ HMu2 _ (hr21 × hr22))

Rel|Rel-[2₂-Fun] :
  (32X @((X11 ~ X12) ~ (X21 ~ X22) ~ (X31 ~ X32)): [32~] [Ob])
  (23VR @(((VR11 × VR21) ~ VRR1) ~ ((VR12 × VR22) ~ VRR2)) :
          (([Rel] (X11 ~ X21) [×] [Rel] (X21 ~ X31)) [~] [Rel] (X11 ~ X31)) [~]
          (([Rel] (X12 ~ X22) [×] [Rel] (X22 ~ X32)) [~] [Rel] (X12 ~ X32)) )
  (3HR @(HR1 ~ HR2 ~ HR3): [Rel|Dup3] 32X)
  (3HV : ([Rel|Rel] _ (VR11 ~ VR12) (HR1 ~ HR2) [×]
          [Rel|Rel] _ (VR21 ~ VR22) (HR2 ~ HR3)) [~]
          [Rel|Rel] _ (VRR1 ~ VRR2) (HR1 ~ HR3))
  (2VMu : Rel-[2-Fun] _ ((VR11 × VR21) ~ VRR1) [~] Rel-[2-Fun] _ ((VR12 × VR22) ~ VRR2))
  → [Any]
Rel|Rel-[2₂-Fun] 32X
  (((VR11 × VR21) ~ VRR1) ~ ((VR12 × VR22) ~ VRR2)) 3HR
  ((HV1 × HV2) ~ HVR) (VMu1 ~ VMu2)
  =
  (32x @((x11 ~ x12) ~ (x21 ~ x22) ~ (x31 ~ x32)) : [Dup3|Dup2] 32X) →
  (22vr @((vr11 × vr21) ~ (vr12 × vr22)) :
          (VR11 (x11 ~ x21) [×] VR21 (x21 ~ x31)) [~]
          (VR12 (x12 ~ x22) [×] VR22 (x22 ~ x32)))
  (3hr @(hr1 ~ hr2 ~ hr3) : [R|Dup3] 3HR 32x)
  (2hv : HV1 _ (vr11 ~ vr12) (hr1 ~ hr2) [×]
         HV2 _ (vr21 ~ vr22) (hr2 ~ hr3)) →
         HVR _ (VMu1 _ (vr11 × vr21) ~ VMu2 _ (vr12 × vr22)) (hr1 ~ hr3)

[22~]-swap₁ : [22~] [Any] → [22~] [Any]
[22~]-swap₁ (2X1 ~ 2X2) = swap 2X1 ~ swap 2X2
[22~]-swap₂ : [22~] [Any] → [22~] [Any]
[22~]-swap₂ (2X1 ~ 2X2) = swap (2X1 ~ 2X2)

Dup|Dup-swap₁ : ∀ {22X} → [Dup2|Dup2] 22X → [Dup2|Dup2] ([22~]-swap₁ 22X)
Dup|Dup-swap₁ (2X1 ~ 2X2) = swap 2X1 ~ swap 2X2
Dup|Dup-swap₂ : ∀ {22X} → [Dup2|Dup2] 22X → [Dup2|Dup2] ([22~]-swap₂ 22X)
Dup|Dup-swap₂ (2X1 ~ 2X2) = swap (2X1 ~ 2X2)

Dup|Rel-swap₁ : ∀ {22X} → [Dup|Rel] 22X → [Dup|Rel] (Dup|Dup-swap₁ 22X)
Dup|Rel-swap₁ (VR1 ~ VR2) = swap (VR1 ~ VR2)
Dup|Rel-swap₂ : ∀ {22X} → [Dup|Rel] 22X → [Dup|Rel] (Dup|Dup-swap₂ 22X)
Dup|Rel-swap₂ (VR1 ~ VR2) = [-] VR1 ~ [-] VR2

Rel|Dup-swap₁ : ∀ {22X} → [Rel|Dup] 22X → [Rel|Dup] (Dup|Dup-swap₁ 22X)
Rel|Dup-swap₁ (HR1 ~ HR2) = [-] HR1 ~ [-] HR2
Rel|Dup-swap₂ : ∀ {22X} → [Rel|Dup] 22X → [Rel|Dup] (Dup|Dup-swap₂ 22X)
Rel|Dup-swap₂ (HR1 ~ HR2) = swap (HR1 ~ HR2)

Rel|Dup-[S-Fun] :
  (22X : [22~] [Ob])
  (22HR : [Rel|Dup] ([22~]-swap₁ 22X) [~] [Rel|Dup] 22X)
  → [Any]
Rel|Dup-[S-Fun] _ ((HR11 ~ HR12) ~ (HR21 ~ HR22)) =
  Rel-[S-Fun] _ (HR11 ~ HR21) [~] Rel-[S-Fun] _ (HR12 ~ HR22)
Dup|Rel-[S-Fun] :
  (22X : [22~] [Ob])
  (22VR : [Dup|Rel] ([22~]-swap₂ 22X) [~] [Dup|Rel] 22X)
  → [Any]
Dup|Rel-[S-Fun] _ ((VR11 ~ VR12) ~ (VR21 ~ VR22)) =
  Rel-[S-Fun] _ (VR11 ~ VR21) [~] Rel-[S-Fun] _ (VR12 ~ VR22)

Rel|Rel-[S₁-Fun] :
  (2X : [2~] [Ob])     (let 22X = 2~|2 2X)
  (2VR : [Dup|Rel] 22X) (let 2VR' = Dup|Rel-swap₁ 2VR)
  (2HR : [Rel|Dup] 22X) (let 2HR' = Rel|Dup-swap₁ 2HR)
  (2HV : [Rel|Rel] 22X 2VR 2HR [~] [Rel|Rel] 22X 2VR' 2HR)
  (2hsymm : Rel|Dup-[S-Fun] _ (2HR ~ 2HR))
  → [Any]
Rel|Rel-[S₁-Fun] 2X 2VR 2HR (HVA ~ HVB) (hsymm1 ~ hsymm2) =
  (22x : [Dup2|Dup2] (2~|2 2X))
  (2vr @(vr1 ~ vr2) : [Dup|R] 2VR 22x)
  (2hr @(hr1 ~ hr2) : [R|Dup] 2HR 22x)
  (let 2vr' = vr2 ~ vr1)
  (let 2hr' = hsymm1 _ hr1 ~ hsymm2 _ hr2)
  (hv : HVA _ 2vr 2hr) → HVB _ 2vr' 2hr'
