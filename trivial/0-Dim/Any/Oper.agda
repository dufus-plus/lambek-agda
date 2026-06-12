open import 0-Dim.Prelude
open import 0-Dim.Any.Defs

-- instances and operations for [Any]

module 0-Dim.Any.Oper where

Fun-Id : Rel-[0Fun] _ (!               > [Fun])
Fun-Mu : Rel-[2Fun] _ (([Fun] × [Fun]) > [Fun])

Fun-Id _ = ⑴
Fun-Mu _ (f₁₂ × f₂₃) = f₁₂ ∘ f₂₃

Rel-Id : Rel-[0Fun] _ (!               > [Rel])
Rel-Op : Rel-[-Fun] _ ((- [Rel])       > [Rel])
Rel-Mu : Rel-[2Fun] _ (([Rel] × [Rel]) > [Rel])
Rel-Comp : (N : [Nat]) →
         Rel-[Fun] _ ([Path] _ [Rel] N > [Rel])

Rel-Id A = [≡] A
Rel-Op _ (- R) = [-] R
Rel-Mu _ (R₁₂ × R₂₃) = R₁₂ [∙] R₂₃
Rel-Comp Zero! _ (≡ A) = [≡] A
Rel-Comp (Succ! N) _ (R ∙ Path) = R [∙] Rel-Comp N _ Path

module _ (2A : [2~] [Ob]) (let RF = Rel-[Fun] 2A) where
  Rel-Fun-Id : Rel-[0Fun] _ (!         > RF)
  Rel-Fun-Mu : Rel-[2Fun] _ ((RF × RF) > RF)

  Rel-Fun-Id _ _ = ⑴
  Rel-Fun-Mu _ (rF₁₂ × rF₂₃) _ = (rF₁₂ _) ∘ (rF₂₃ _)

-- test for inference
private module Test-Rel-Fun (2A : [2~] [Ob]) (R : [Rel] 2A) where
  test-Id : Rel-[Fun] _ (R > R)
  test-Id = Rel-Fun-Id _ R

  test-Mu : Rel-[Fun] _ (R > R)
  test-Mu = Rel-Fun-Mu _ _ (test-Id × test-Id)

module _ (2A : [2~] [Ob]) (let RR = Rel-[Rel] 2A) where
  Rel-Rel-Id : Rel-[0Fun] _ (!         > RR)
  Rel-Rel-Op : Rel-[-Fun] _ ((- RR)    > RR)
  Rel-Rel-Mu : Rel-[2Fun] _ ((RR × RR) > RR)

  Rel-Rel-Id R 2a = [≡] (R 2a)
  Rel-Rel-Op _ (- rR) _ = [-] (rR _)
  Rel-Rel-Mu _ (rR₁₂ × rR₂₃) _ = (rR₁₂ _) [∙] (rR₂₃ _)

-- test for inference
private module Test-Rel-Rel (2A : [2~] [Ob]) (R : [Rel] 2A) where
  test-Id : Rel-[Rel] _ (R > R)
  test-Id = Rel-Rel-Id _ R

  test-Op : Rel-[Rel] _ (R > R)
  test-Op = Rel-Rel-Op _ _ (- test-Id)

  test-Mu : Rel-[Rel] _ (R > R)
  test-Mu = Rel-Rel-Mu _ _ (test-Id × test-Id)

-- data [Rel|≡] {2A : [2~Ob]} (R : [Rel] 2A) :
--     [Rel|Rel] _ ([≡] _ ~ [≡] _) (R ~ R) where
--   Rel|≡ : {2a : [Dup2] 2A} → (r : R 2a) → [Rel|≡] R _ ((≡ _) ~ (≡ _)) (r ~ r)

-- data [≡|Rel] {2A : [2~Ob]} (R : [Rel] 2A) :
--     [Rel|Rel] _ (R ~ R) ([≡] _ ~ [≡] _) where
--   ≡|Rel : {2a : [Dup2] 2A} → (r : R 2a) → [≡|Rel] R _ (r ~ r) ((≡ _) ~ (≡ _))

-- [Rel|≡]: : [Rel|Rel] _ ([≡] _ ~ [≡] _) ([Rel] ~ [Rel])
-- [Rel|≡]: = [Rel|≡] [Rel]
-- [≡|Rel]: : [Rel|Rel] _ ([Rel] ~ [Rel]) ([≡] _ ~ [≡] _)
-- [≡|Rel]: = [≡|Rel] [Rel]

-- Dup|Rel-Id : (22A : [22~Ob]) (2VI : [Dup|≡] 22A) → [Dup|Rel] 22A
-- Dup|Rel-Id _ (VI₁ ~ VI₂) = Rel-Id _ VI₁ ~ Rel-Id _ VI₂
-- Rel-Id|Dup : (22A : [22~Ob]) (2VI : [≡|Dup] 22A) → [Rel|Dup] 22A
-- Rel-Id|Dup _ (HI₁ ~ HI₂) = Rel-Id _ HI₁ ~ Rel-Id _ HI₂

-- [Dup|∙] = [Dup|R] (2~ ([Rel] [∙] [Rel]))
-- [∙|Dup] = [R|Dup] (2~ ([Rel] [∙] [Rel]))

-- Dup|Rel-Mu : (22A : [22~Ob]) (2V∙VR : [Dup|∙] 22A) → [Dup|Rel] 22A
-- Dup|Rel-Mu _ ((VR₁₀1 ∙ VR₀₂1) ~ (VR₁₀2 ∙ VR₀₂2)) = (VR₁₀1 [∙] VR₀₂1) ~ (VR₁₀2 [∙] VR₀₂2)
-- Rel-Mu|Dup : (22A : [22~Ob]) (2V∙VR : [∙|Dup] 22A) → [Rel|Dup] 22A
-- Rel-Mu|Dup _ ((VR₁₀1 ∙ VR₀₂1) ~ (VR₁₀2 ∙ VR₀₂2)) = (VR₁₀1 [∙] VR₀₂1) ~ (VR₁₀2 [∙] VR₀₂2)

-- Rel|Rel-Id :
--   (22A : [22~Ob])
--   (2VI : [Dup|≡]   22A)
--   (2HR : [Rel|Dup] 22A) →
--   [Rel|≡]: _ 2VI 2HR →
--   [Rel|Rel] _ (Dup|Rel-Id _ 2VI) 2HR
-- Rel|Rel-Id _ ((≡ _) ~ (≡ _)) _ (Rel|≡ R) = [Rel|≡] R

-- Rel-Id|Rel :
--   (22A : [22~Ob])
--   (2VR : [Dup|Rel] 22A)
--   (2HI : [≡|Dup]   22A) →
--   [≡|Rel]: _ 2VR 2HI →
--   [Rel|Rel] _ 2VR (Rel-Id|Dup _ 2HI)
-- Rel-Id|Rel _ _ ((≡ _) ~ (≡ _)) (≡|Rel R) = [≡|Rel] R

-- RR-flip :
--   {((X11 ~ X12) ~ (X21 ~ X22)) : ([Any] [~] [Any]) [~] ([Any] [~] [Any])}
--   {(VR1 ~ VR2) : [Rel] (X11 ~ X21) [~] [Rel] (X12 ~ X22)}
--   {(HR1 ~ HR2) : [Rel] (X11 ~ X12) [~] [Rel] (X21 ~ X22)} →
--   [Rel|Rel] _ (VR1 ~ VR2) (HR1 ~ HR2) → [Rel|Rel] _ (HR1 ~ HR2) (VR1 ~ VR2)
-- RR-flip RR _ hr12 vr12 = RR _ vr12 hr12

-- module _
--     (22A : [22~Ob])
--     (2V∙VR @((_∙_ {A₀1} VR₋₀1 VR₀₊1) ~ (_∙_ {A₀2} VR₋₀2 VR₀₊2)) :
--       [Dup|R] (2~ ([Rel] [∙] [Rel])) 22A)
--     (2HR : [Rel|Dup] 22A)
--     (2RR @(_∙_ {HR₀} RR₋₀ RR₀₊) :
--       ([Rel|Rel] _ (VR₋₀1 ~ VR₋₀2) [∙] [Rel|Rel] _ (VR₀₊1 ~ VR₀₊2)) 2HR)
--     (22a : [Dup|Dup] 22A)
--     (2v∙vr @((_∙_ {a₀1} vr₋₀1 vr₀₊1) ~ (_∙_ {a₀2} vr₋₀2 vr₀₊2)) :
--       [Dup|R] (Dup|Rel-Mu _ 2V∙VR) 22a)
--     (2hr @(hr₋ ~ hr₊) : [R|Dup] 2HR 22a)
--     where
--   record [Rel|∙] : [Any] where
--     constructor _∙_
--     field {$hr₀} : HR₀ (a₀1 ~ a₀2)
--     field $rr₋₀ : RR₋₀ _ (vr₋₀1 ~ vr₋₀2) (hr₋ ~ $hr₀)
--     field $rr₀₊ : RR₀₊ _ (vr₀₊1 ~ vr₀₊2) ($hr₀ ~ hr₊)
--   open [Rel|∙] public

-- module _
--     (22A : [22~Ob])
--     (2VR : [Dup|Rel] 22A)
--     (2H∙HR @((_∙_ {A₀1} HR₋₀1 HR₀₊1) ~ (_∙_ {A₀2} HR₋₀2 HR₀₊2)) :
--       [R|Dup] (2~ ([Rel] [∙] [Rel])) 22A)
--     (2RR @(_∙_ {VR₀} RR₋₀ RR₀₊) :
--       (RR-flip [Rel|Rel] _ (HR₋₀1 ~ HR₋₀2) [∙] RR-flip [Rel|Rel] _ (HR₀₊1 ~ HR₀₊2)) 2VR)
--     (22a : [Dup|Dup] 22A)
--     (2vr @(vr₋ ~ vr₊) : [Dup|R] 2VR 22a)
--     (2h∙hr @((_∙_ {a₀1} hr₋₀1 hr₀₊1) ~ (_∙_ {a₀2} hr₋₀2 hr₀₊2)) :
--       [R|Dup] (Rel-Mu|Dup _ 2H∙HR) 22a)
--     where
--   record [∙|Rel] : [Any] where
--     constructor _∙_
--     field {$vr₀} : VR₀ (a₀1 ~ a₀2)
--     field $rr₋₀ : RR₋₀ _ (vr₋ ~ $vr₀) (hr₋₀1 ~ hr₋₀2)
--     field $rr₀₊ : RR₀₊ _ ($vr₀ ~ vr₊) (hr₀₊1 ~ hr₀₊2)
--   open [∙|Rel] public

-- [Rel|∙]: : [Rel|Rel] _ (([Rel] [∙] [Rel]) ~ ([Rel] [∙] [Rel])) ([Rel] ~ [Rel])
-- [Rel|∙]: = [Rel|∙] _ (([Rel] ∙ [Rel]) ~ ([Rel] ∙ [Rel])) ([Rel] ~ [Rel]) ([Rel|Rel] ∙ [Rel|Rel])
-- [∙|Rel]: : [Rel|Rel] _ ([Rel] ~ [Rel]) (([Rel] [∙] [Rel]) ~ ([Rel] [∙] [Rel]))
-- [∙|Rel]: = [∙|Rel] _ ([Rel] ~ [Rel]) (([Rel] ∙ [Rel]) ~ ([Rel] ∙ [Rel])) ([Rel|Rel] ∙ [Rel|Rel])

-- Rel|Rel-Mu :
--   (22A : [22~Ob])
--   (2V∙VR : [Dup|R] (2~ ([Rel] [∙] [Rel])) 22A)
--   (2HR : [Rel|Dup] 22A) →
--   (2RR : [Rel|∙]: 22A 2V∙VR 2HR) →
--   [Rel|Rel] _ (Dup|Rel-Mu _ 2V∙VR) 2HR
-- Rel|Rel-Mu _ _ _ (RR₁₀ ∙ RR₀₂) = [Rel|∙] _ _ _ (RR₁₀ ∙ RR₀₂)

-- Rel-Mu|Rel :
--   (22A : [22~Ob])
--   (2VR : [Dup|Rel] 22A) →
--   (2H∙HR : [R|Dup] (2~ ([Rel] [∙] [Rel])) 22A)
--   (2RR : [∙|Rel]: 22A 2VR 2H∙HR) →
--   [Rel|Rel] _ 2VR (Rel-Mu|Dup _ 2H∙HR)
-- Rel-Mu|Rel _ _ _ (RR₁₀ ∙ RR₀₂) = [∙|Rel] _ _ _ (RR₁₀ ∙ RR₀₂)

-- private module Test-Rel|Rel-Id-Mu where
--   test-VId :
--     ((A ~ B) : [Ob] [~] [Ob]) (R : [Rel] (A ~ B)) →
--     [Rel|Rel] _ ([≡] _ ~ [≡] _) (R ~ R)
--   test-VId _ R = Rel|Rel-Id _ ((≡ _) ~ (≡ _)) _ (Rel|≡ R)

--   test-VMu :
--     ((A ~ B) : [Ob] [~] [Ob]) (R : [Rel] (A ~ B)) →
--     [Rel|Rel] _ (([≡] _ [∙] [≡] _) ~ ([≡] _ [∙] [≡] _)) (R ~ R)
--   test-VMu _ R = Rel|Rel-Mu _ _ _ (test-VId _ R ∙ test-VId _ R)
