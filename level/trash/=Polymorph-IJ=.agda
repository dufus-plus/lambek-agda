import =Curry=
import =Bishop-omegaType=

module =Polymorph-IJ= where

open =Curry=
open =Bishop-omegaType=

-- inter-universal setoid theory
-- represents level-indexed cups of level-indexed caps of the level-polymophic element type
module Inter where

  record [#Ob] : LevelUniv₁ where
    constructor !
    field [i] [j] : LevelUniv₀
    field [%Ok] : LevelUniv₀
    field %Ok-Refl : [%Ok]
    field %Ok-Symm : (%ok₂₁ : [%Ok]) → [%Ok]
    field %Ok-Tran : (%ok₁₂ %ok₂₃ : [%Ok]) → [%Ok]
    field [%To] : LevelUniv₀
    field %To-Refl : [%To]
    field %To-Symm : (%to₂₁ : [%To]) → [%To]
    field %To-Tran : (%to₁₂ %to₂₃ : [%To]) → [%To]
    field El% : (i : [i]) → (j : [j]) → [Level]
    field Ok% : (i : [i]) (j₁ j₂ : [j]) → (%ok : [%Ok]) → [Level]
    field To% : (i₁ i₂ : [i]) (j : [j]) → (%to : [%To]) → [Level]
  -- Σ Π 
  module _ (# : [#Ob]) where
    module :[Ob] where
      open [#Ob] #
      :[El*] = ∀ i j → Type (El% i j)
      module _ ([El*] : :[El*]) where
        :[Ok*] = 
          ∀ {i j₁ j₂} → (%ok : [%Ok]) → 
          (el₁ : [El*] i j₁) → (el₂ : [El*] i j₂) → Type (Ok% i j₁ j₂ %ok)
        :[To*] = 
          ∀ {i₁ i₂ j} → (%to : [%To]) → 
          (el₁ : [El*] i₁ j) → (el₂ : [El*] i₂ j) → Type (To% i₁ i₂ j %to)
        module _ ([Ok*] : :[Ok*]) where
          -- inter-universal Ok coReflectivity
          :Ok-coRefl* = 
            ∀ {i j} (let %ok = %Ok-Refl) (el el' : [El*] i j) → 
            (ok : [Ok*] %ok el el') → Type.[≡] el el' 
          -- inter-universal Ok coSymmetry
          :Ok-coSymm* = 
            ∀ {i j₁ j₂} {%ok₂₁ : [%Ok]} (let %ok₁₂ = %Ok-Symm %ok₂₁)  
            {el₁ : [El*] i j₁} → {el₂ : [El*] i j₂} →  
            (ok₂₁ : [Ok*] %ok₂₁ el₂ el₁) → [Ok*] %ok₁₂ el₁ el₂ 
          -- inter-universal Ok coTransitivity
          :Ok-coTran* = 
            ∀ {i j₁ j₂ j₃} {%ok₁₂ %ok₂₃ : [%Ok]}
            (let %ok₁₃ = %Ok-Tran %ok₁₂ %ok₂₃) →  
            {el₁ : [El*] i j₁} → {el₂ : [El*] i j₂} → {el₃ : [El*] i j₃} → 
            (ok₁₂ : [Ok*] %ok₁₂ el₁ el₂) → (ok₂₃ : [Ok*] %ok₂₃ el₂ el₃) → [Ok*] %ok₁₃ el₁ el₃ 
          record :is-coEqu* : ωType where
            constructor ‼
            field coRefl* : :Ok-coRefl*
            field coSymm* : :Ok-coSymm*
            field coTran* : :Ok-coTran* 
        module _ ([To*] : :[To*]) where
          -- inter-universal To Reflectivity
          :To-Refl* = 
            ∀ {i j} (let %to = %To-Refl) (el : [El*] i j) → [To*] %to el el 
          -- inter-universal To coSymmetry
          :To-Symm* = 
            ∀ {i₁ i₂ j} {%to₂₁ : [%To]} (let %to₁₂ = %To-Symm %to₂₁)  
            {el₁ : [El*] i₁ j} → {el₂ : [El*] i₂ j} →  
            (ok₂₁ : [To*] %to₂₁ el₂ el₁) → [To*] %to₁₂ el₁ el₂ 
          -- inter-universal To Transitivity
          :To-Tran* = 
            ∀ {i₁ i₂ i₃ j} {%to₁₂ %to₂₃ : [%To]} 
            (let %to₁₃ = %To-Tran %to₁₂ %to₂₃) →  
            {el₁ : [El*] i₁ j} → {el₂ : [El*] i₂ j} → {el₃ : [El*] i₃ j} → 
            (to₁₂ : [To*] %to₁₂ el₁ el₂) → (to₂₃ : [To*] %to₂₃ el₂ el₃) → [To*] %to₁₃ el₁ el₃ 
          record :is-Equ* : ωType where
            constructor ‼
            field Refl* : :To-Refl*
            field Symm* : :To-Symm*
            field Tran* : :To-Tran*         
    -- open :[Ob].:is-Equ* public
    -- open :[Ob].:is-coEqu* public 

    record [Ob] : ωType where
      constructor !
      open :[Ob]
      field [El*] : :[El*]
      field [Ok*] : :[Ok*] [El*]
      field [To*] : :[To*] [El*]
      field Ok-is-coEqu* : :is-coEqu* [El*] [Ok*]
      field To-is-Equ*   : :is-Equ*   [El*] [To*]
      open :is-coEqu* Ok-is-coEqu* public
      open :is-Equ* To-is-Equ* public

  module _ {# : [#Ob]} where
    open [#Ob] # 
    record [Poly] (O : [Ob] #) : ωType where
      constructor ‼
      open [Ob] O 
      field pi  : [i]
      field pEl : ∀ j → [El*] pi j
      field pOk : ∀ %ok j₁ j₂ → [Ok*] %ok (pEl j₁) (pEl j₂)
    open [Poly] public

    record Poly-[To] {O : [Ob] #} (p₁ p₂ : [Poly] O) : ωType where
      constructor ‼
      open [Ob] O
      field p%to : [%To]
      field pTo : ∀ j → [To*] p%to (p₁ .pEl j) (p₂ .pEl j)
    open Poly-[To] public
  
    module Def-Poly (O : [Ob] #) where
      open [Ob] O
      Poly : [ωSet]        
      Poly .[El] = [Poly] O
      Poly .[To] = Poly-[To]
      Poly .Refl p .p%to = %To-Refl
      Poly .Refl p .pTo j = Refl* (p .pEl j)
      Poly .Symm pto21 .p%to = %To-Symm (pto21 .p%to)
      Poly .Symm pto21 .pTo j = Symm* (pto21 .pTo j)
      Poly .Tran pto12 pto23 .p%to = %To-Tran (pto12 .p%to) (pto23 .p%to)
      Poly .Tran pto12 pto23 .pTo j = Tran* (pto12 .pTo j) (pto23 .pTo j)

  open [#Ob] public

  module _ (#A #B : [#Ob]) where
    record [Fun#]-i : LevelUniv₀ where
      constructor !
      field fi : #A .[i] → #B .[i]
      field fj : #B .[j] → #A .[j]
    open [Fun#]-i public
    record [Fun#]-j : LevelUniv₀ where
      constructor !
      field ai : #A .[i]
      field bj : #B .[j]
    open [Fun#]-j public
    
    Fun# : [#Ob]
    Fun# .[i] = [Fun#]-i
    Fun# .[j] = [Fun#]-j
    -- field [%Ok] : LevelUniv₀
    -- field %Ok-Refl : [%Ok]
    -- field %Ok-Symm : (%ok₂₁ : [%Ok]) → [%Ok]
    -- field %Ok-Tran : (%ok₁₂ %ok₂₃ : [%Ok]) → [%Ok]
    -- field [%To] : LevelUniv₀
    -- field %To-Refl : [%To]
    -- field %To-Symm : (%to₂₁ : [%To]) → [%To]
    -- field %To-Tran : (%to₁₂ %to₂₃ : [%To]) → [%To]
    -- field El% : (i : [i]) → (j : [j]) → [Level]
    -- field Ok% : (i : [i]) (j₁ j₂ : [j]) → (%ok : [%Ok]) → [Level]
    -- field To% : (i₁ i₂ : [i]) (j : [j]) → (%to : [%To]) → [Level]
    Fun# .el% i j = #A. el% (j .ai) (i .fj← (j .bj)) ⊔ #B. el% (i .fi→ (j .ai)) (j .bj)
    Fun# .ok% i j1 j2 = 0% 
    Fun# .to% i1 i2 j = 0%

  module _ {#A #B : [#Ob]} (A : [Ob] #A) (B : [Ob] #B) where
    open [Ob]:
    
    Fun-[El] : :[El] (Fun# #A #B)
    Fun-[El] i j = A. [El] (j .ai) (i .fj← (j .bj)) → B. [El] (i .fi→ (j .ai)) (j .bj)

--     module _ (i : [Fun#]-i #A #B) (j1 j2 : [Fun#]-j #A #B) 
--         (f1 : Fun-[El] i j1) (f2 : Fun-[El] i j2) where
--       record [Fun]-Ok : ωType where
--         field fOk : Ord.[Rel|Fun] f1 f2 (A .Ok ai aj aj) (B .Ok bj1 bj2)
--       open [Fun]-Ok public
--     -- Fun : [Ob] (Fun# #A #B)
--     -- Fun .[El] i j = 
--     -- Fun .Ok i j1 j2  = record where
--     -- --   rEl f1 f2 = 
      