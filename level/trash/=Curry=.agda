import Agda.Primitive

--
-- type-theoretical prelude goes here
--
module =Curry= where

module Prelude where
  open Agda.Primitive 
    using (LevelUniv; _⊔_) 
    renaming (Set to Type; Setω to ωType; Level to [Level]; lzero to 0%; lsuc to 1+_) 
    public

  -- since we have not (LevelUnivₙ)
  LevelUniv₀ = LevelUniv
  LevelUniv₁ = Type₁
  LevelUniv₂ = Type₂

  record ωLift {%1 : [Level]} ([1] : Type %1) : ωType where
    constructor ↑ 
    field ↓ : [1]
  open ωLift public

  record [!] : Type where
    constructor !

  module _ {%1 %2 : [Level]} where
    record _[×]_ ([1] : Type %1) ([2] : Type %2) : Type (%1 ⊔ %2) where
      constructor _×_ 
      field ₁ : [1]
      field ₂ : [2]
    open _[×]_ public

  module _ {%0 : [Level]} {[0] : Type %0} where
    ⑴ : [0] → [0]
    ⑴ x = x
  module _ {[0] : ωType} where
    ω⑴ : [0] → [0]
    ω⑴ x = x

  
  module _ {%1 %2 %3 : [Level]} where
    module _ {[1] : Type %1} {[2] : Type %2} {[3] : Type %3} where
      _∘_ : ([1] → [2]) → ([2] → [3]) → ([1] → [3])
      (f ∘ g) a = g (f a)

  module _ {[1] : ωType} {[2] : ωType} {[3] : ωType} where
      _ω∘_ : ([1] → [2]) → ([2] → [3]) → ([1] → [3])
      (f ω∘ g) a = g (f a)

  module _ {%1 %2 %3 %R12 %R23 : [Level]} where
    module _ {[1] : Type %1} {[2] : Type %2} {[3] : Type %3}
             ([R12] : [1] → [2] → Type %R12) ([R23] : [2] → [3] → Type %R23) where
      record _[∙]_ (₁ : [1]) (₃ : [3]) : Type (%2 ⊔ %R12 ⊔ %R23) where
        constructor _∙_
        field {₂} : [2]
        field ₁₂ : [R12] ₁ ₂
        field ₂₃ : [R23] ₂ ₃
      open _[∙]_ public

  module _ {[1] : ωType} {[2] : ωType} {[3] : ωType}
             ([R12] : [1] → [2] → ωType) ([R23] : [2] → [3] → ωType) where
      record _ω[∙]_ (₁ : [1]) (₃ : [3]) : ωType where
        constructor _∙_
        field {₂} : [2]
        field ₁₂ : [R12] ₁ ₂
        field ₂₃ : [R23] ₂ ₃
      open _ω[∙]_ public

open Prelude public

module Level where

  data [≡] {[A] : LevelUniv} : [A] → [A] → LevelUniv where
    instance ≡ : {a : [A]} → [≡] a a

  module _ {[A] : LevelUniv} where
    ≡-Refl : (a : [A]) → [≡] a a 
    ≡-Refl _ = ≡
    ≡-Symm : {a1 a2 : [A]} → [≡] a2 a1 → [≡] a1 a2
    ≡-Symm ≡ = ≡
    ≡-Tran : {a1 a2 a3 : [A]} → [≡] a1 a2 → [≡] a2 a3 → [≡] a1 a3
    ≡-Tran ≡ ≡ = ≡

module Type where

  data [≡] {%A} {[A] : Type %A} (a : [A]): [A] → Type 0% where
    instance ≡ : [≡] a a

  module _ {%A} {[A] : Type %A} where
    ≡-Refl : (a : [A]) → [≡] a a 
    ≡-Refl _ = ≡
    ≡-Symm : {a1 a2 : [A]} → [≡] a2 a1 → [≡] a1 a2
    ≡-Symm ≡ = ≡
    ≡-Tran : {a1 a2 a3 : [A]} → [≡] a1 a2 → [≡] a2 a3 → [≡] a1 a3
    ≡-Tran ≡ ≡ = ≡

  module _ (%Ob : [Level]) where
    [Ob] : Type (1+ %Ob)
    [Ob] = Type %Ob

  Ob-Id : [Ob] 0%
  Ob-Id = [!] 

  module _ {%1 %2 : [Level]} where
    module _ ([1] : [Ob] %1) ([2] : [Ob] %2) where
      Ob-Mu : [Ob] (%1 ⊔ %2)
      Ob-Mu = [1] [×] [2]

  module _ {%1 %2 : [Level]} where
    module _ ([1] : [Ob] %1) ([2] : [Ob] %2) where
      [Fun] : Type (%1 ⊔ %2)
      [Fun] = [1] → [2]

  module _ {%1 %2 : [Level]} (%Rel : [Level]) where
    module _ ([1] : [Ob] %1) ([2] : [Ob] %2) where
      [Rel] : Type (%1 ⊔ %2 ⊔ 1+ %Rel)
      [Rel] = [1] → [2] → Type %Rel

  Fun-Id = ⑴
  Fun-Mu = _∘_

  -- Rel-Id -- no identity types
  Rel-Mu = _[∙]_

  module _ {%1 %2 : [Level]} where
    module _ ([1] : [Ob] %1) ([2] : [Ob] %2) where
      Const : [2] → ([1] → [2])
      Const y _ = y

  module _ ([1] : ωType) ([2] : ωType) where
      ωConst : [2] → ([1] → [2])
      ωConst y _ = y
