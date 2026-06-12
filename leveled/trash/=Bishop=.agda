import =Curry=

module =Bishop= where

open =Curry=

-- components of the double category of SOrders
module Ord where

  record [%Ob] : LevelUniv where
    constructor !
    field El : [Level]
    field To : [Level]
  open [%Ob] public 

  -- objects of category of Orders
  module _ (% : [%Ob]) where
    Ob% = 1+ (% .El) ⊔ 1+ (% .To)
    record [Ob] : Type Ob% where
      constructor !
      field [El] : Type (% .El)
      field [To] : (el el' : [El]) → Type (% .To)
      field Refl : ∀ el0 → [To] el0 el0
      -- field Symm : ∀ el1 el2 → (to21 : [To] el2 el1) → [To] el1 el2
      field Tran : ∀ el1 el2 el3 → (to12 : [To] el1 el2) → (to23 : [To] el2 el3) → [To] el1 el3
    open [Ob] public
  
  -- function morphisms
  Fun%-Ob : (%1 %2 : [%Ob]) → [Level]
  Fun%-Ob %1 %2 = %1 .El ⊔ %2 .El ⊔ %1 .To ⊔ %2 .To
  module _ {%1 %2 : [%Ob]} where    
    module _ (O1 : [Ob] %1) (O2 : [Ob] %2) where
      record [Fun] : Type (Fun%-Ob %1 %2) where
        constructor !
        field fEl : O1 .[El] → O2 .[El]
        field fTo : ∀ el1 el2 → O1 .[To] el1 el2 → O2 .[To] (fEl el1) (fEl el2)
      open [Fun] public

  -- relation morphisms
  [%Rel] = [Level]
  Rel%-Ob : (%1 %2 : [%Ob]) → [%Rel] → [Level]
  Rel%-Ob %1 %2 %rEl = %1 .El ⊔ %2 .El ⊔ %1 .To ⊔ %2 .To ⊔ 1+ %rEl
  module _ {%1 %2 : [%Ob]} (%rEl : [%Rel]) where
    module _ (O1 : [Ob] %1) (O2 : [Ob] %2) where
      record [Rel] : Type (Rel%-Ob %1 %2 %rEl) where
        constructor ! 
        field [rEl] : O1 .[El] → O2 .[El] → Type %rEl
        field LTran : ∀ ael ael' bel → O1 .[To] ael ael' → [rEl] ael' bel → [rEl] ael bel
        field RTran : ∀ ael bel bel' → [rEl] ael bel → O2 .[To] bel bel' → [rEl] ael bel'
      open [Rel] public

  Fun%-To : (%1 %2 : [%Ob]) → [Level]
  Fun%-To %1 %2 = %1 .El ⊔ %2 .To
  module _ {%1 %2 : [%Ob]} where
    module _ {O1 : [Ob] %1} {O2 : [Ob] %2} where
      [FunTo] : (f g : [Fun] O1 O2) → Type (Fun%-To %1 %2)
      [FunTo] f g = ∀ a → O2 .[To] (f .fEl a) (g .fEl a)

  Rel%-To : (%1 %2 : [%Ob]) → (%R1 %R2 : [Level]) → [Level]
  Rel%-To %1 %2 %R1 %R2 = %1 .El ⊔ %2 .El ⊔ %R1 ⊔ %R2
  module _ {%1 %2 : [%Ob]} {%R1 %R2 : [Level]} where
    module _ {O1 : [Ob] %1} {O2 : [Ob] %2} where
      [RelTo] : (R1 : [Rel] %R1 O1 O2) → (R2 : [Rel] %R2 O1 O2) → Type (Rel%-To %1 %2 %R1 %R2)
      [RelTo] R1 R2 = ∀ a b → R1 .[rEl] a b → R2 .[rEl] a b

  module _ {% : [%Ob]} (O : [Ob] %) where
    Opp : [Ob] %
    Opp .[El] = O .[El]
    Opp .[To] o o' = O .[To] o' o
    Opp .Refl = O .Refl
    Opp .Tran _ _ _ ato12 ato23 = O .Tran _ _ _ ato23 ato12 

  Fun% : (%1 %2 : [%Ob]) → [%Ob]
  Fun% %1 %2 .El = Fun%-Ob %1 %2  
  Fun% %1 %2 .To = Fun%-To %1 %2

  module _ {%1 %2 : [%Ob]} where
    module _ (O1 : [Ob] %1) (O2 : [Ob] %2) where
        Funᵒ : [Ob] (Fun% %1 %2)  
        Funᵒ .[El] = [Fun] O1 O2 
        Funᵒ .[To] f g = [FunTo] f g
        Funᵒ .Refl _ a = O2 .Refl _
        Funᵒ .Tran _ _ _ fto12 fto23 a = O2 .Tran _ _ _ (fto12 a) (fto23 a)

  Rel% : (%1 %2 : [%Ob]) → (%R : [Level]) → [%Ob]
  Rel% %1 %2 %R .El = Rel%-Ob %1 %2 %R
  Rel% %1 %2 %R .To = %1 .El ⊔ %2 .El ⊔ %R

  module _ {%1 %2 : [%Ob]} (%R : [%Rel]) where
    module _ (O1 : [Ob] %1) (O2 : [Ob] %2) where
        Relᵒ : [Ob] (Rel% %1 %2 %R)
        Relᵒ .[El] = [Rel] %R O1 O2 
        Relᵒ .[To] R R' = [RelTo] R R'
        Relᵒ .Refl R a b = ⑴
        Relᵒ .Tran R1 R2 R3 rto12 rto23 a b = rto12 a b ∘ rto23 a b

  module _ {% : [%Ob]} (O : [Ob] %) where
    Fun-Id : [Fun] O O
    Fun-Id = record where
      fEl = ⑴  
      fTo _ _ = ⑴ 
    Rel-Id : [Rel] (% .To) O O 
    Rel-Id = record where
      [rEl] = O .[To]
      LTran = O .Tran 
      RTran = O .Tran 

  module _ {%1 %2 %3 : [%Ob]} where
    module _ {O1 : [Ob] %1} {O2 : [Ob] %2} {O3 : [Ob] %3} where
      Fun-Mu : [Fun] O1 O2 → [Fun] O2 O3 → [Fun] O1 O3
      Fun-Mu fab fbc .fEl = fab .fEl ∘ fbc .fEl
      Fun-Mu fab fbc .fTo _ _ = fab .fTo _ _ ∘ fbc .fTo _ _

  module _ {%1 %2 %3 : [%Ob]} {%R12 %R23 : [%Rel]} where
    module _ {O1 : [Ob] %1} {O2 : [Ob] %2} {O3 : [Ob] %3} where
      Rel-Mu : [Rel] %R12 O1 O2 → [Rel] %R23 O2 O3 → [Rel] (%2 .El ⊔ %R12 ⊔ %R23) O1 O3
      Rel-Mu Rab Rbc .[rEl] = (Rab .[rEl]) [∙] (Rbc .[rEl])
      Rel-Mu Rab Rbc .LTran _ _ _ aeq12 (rab ∙ rbc) = (Rab .LTran _ _ _ aeq12 rab) ∙ rbc
      Rel-Mu Rab Rbc .RTran _ _ _ (rab ∙ rbc) ceq12 = rab ∙ (Rbc .RTran _ _ _ rbc ceq12)
  
  -- representable and corepresentable relation
  module _ {%1 %2 : [%Ob]} where
    module _ {O1 : [Ob] %1} {O2 : [Ob] %2} where
      Rep+ : [Fun] O1 O2 → [Rel] (%2 .To) O1 O2
      Rep+ f .[rEl] a b = O2 .[To] (f .fEl a) b
      Rep+ f .LTran a1 a2 b ato12 rab = O2 .Tran _ _ _ (f .fTo _ _ ato12) rab
      Rep+ f .RTran a b1 b2 rab bto12 = O2 .Tran _ _ _ rab bto12
    
      Rep- : [Fun] O1 O2 → [Rel] (%2 .To) O2 O1
      Rep- f .[rEl] b a = O2 .[To] b (f .fEl a)
      Rep- f .LTran b1 b2 a bto12 rab = O2 .Tran _ _ _ bto12 rab
      Rep- f .RTran b a1 a2 rab ato12 = O2 .Tran _ _ _ rab (f .fTo _ _ ato12)

  module _ {%1 %2 : [%Ob]} where
    module _ (O1 : [Ob] %1) (O2 : [Ob] %2) where
      Const : O2 .[El] → [Fun] O1 O2
      Const b .fEl = Type.Const (O1 .[El]) (O2 .[El]) b
      Const b .fTo _ _ _ = O2 .Refl b 

  module _ {%11 %12 %21 %22 : [%Ob]} {%R : [%Rel]} where
    module _ {O11 : [Ob] %11} {O12 : [Ob] %12} 
             {O21 : [Ob] %21} {O22 : [Ob] %22} where
      Rel-Up : [Fun] O11 O21 → [Fun] O12 O22 → [Rel] %R O21 O22 → [Rel] %R O11 O12
      Rel-Up v1 v2 h .[rEl] a11 a12 = h .[rEl] (v1 .fEl a11) (v2 .fEl a12)
      Rel-Up v1 v2 h .LTran a11 a11' a12 a11to r = 
        h .LTran (v1 .fEl a11) (v1 .fEl a11') (v2 .fEl a12) (v1 .fTo a11 a11' a11to) r
      Rel-Up v1 v2 h .RTran a11 a12 a12' r a12to = 
        h .RTran (v1 .fEl a11) (v2 .fEl a12) (v2 .fEl a12') r (v2 .fTo a12 a12' a12to)

  module _ {%11 %12 %21 %22 : [%Ob]} where
    module _ {O11 : [Ob] %11} {O12 : [Ob] %12} 
             {O21 : [Ob] %21} {O22 : [Ob] %22} where
      module _ (v1 : [Fun] O11 O21)(v2 : [Fun] O12 O22)
               (h1 : [Fun] O11 O12)(h2 : [Fun] O21 O22) where
        record [Fun|Fun] : Type (%11 .El ⊔ %22 .To) where 
          constructor ↑
          field ↓ : [FunTo] (Fun-Mu v1 h2) (Fun-Mu h1 v2)
        open [Fun|Fun] public
      module _ {%h1 %h2 : [%Rel]}
               (v1 : [Fun] O11 O21)(v2 : [Fun] O12 O22)
               (h1 : [Rel] %h1 O11 O12)(h2 : [Rel] %h2 O21 O22) where
        record [Rel|Fun] : Type (%11 .El ⊔ %12 .El ⊔ %h1 ⊔ %h2) where
          constructor ↑ 
          field ↓ : [RelTo] h1 (Rel-Up v1 v2 h2)
        open [Rel|Fun] public

  module _ {%1 %2 : [%Ob]} where
    module _ {O1 : [Ob] %1} {O2 : [Ob] %2} where
      module _ (f : [Fun] O1 O2) where
        Rel-Id|Fun : [Rel|Fun] f f (Rel-Id O1) (Rel-Id O2)
        Rel-Id|Fun .↓ = f .fTo
  --

  -- -- just (E)ndo-(F)unctors on (O)rders
  -- record [EFO] : Type where
  --   constructor !
  --   field f-Ob : [Ob] %El1 %To1 → [Ob] %El2 %To2
  --   field f-Fun : ∀ {A B} → [Fun] A B → [Fun] (f-Ob A) (f-Ob B)
  --   field f-Rel : ∀ {A B} → [Rel] A B → [Rel] (f-Ob A) (f-Ob B)
  --   field 
  --    f-Rel|Fun : 
  --     ∀ {A11 A12 A21 A22} →
  --       {v1 : [Fun] A11 A21} {v2 : [Fun] A12 A22} {h1 : [Rel] A11 A12} {h2 : [Rel] A21 A22} →
  --       [Rel|Fun] v1 v2 h1 h2 → 
  --       [Rel|Fun] (f-Fun v1) (f-Fun v2) (f-Rel h1) (f-Rel h2) 
  --   -- field fun-id
  --   -- field fun-mu
  --   field rel-id-to : ∀ {A} → [RelTo] (Rel-Id (f-Ob A)) (f-Rel (Rel-Id A))
  --   field rel-id-fr : ∀ {A} → [RelTo] (f-Rel (Rel-Id A)) (Rel-Id (f-Ob A))
  -- open [EFO] public

--

-- make record fields visible outside w/o module prefix
open Ord.[%Ob] public
open Ord.[Ob] public
open Ord.[Fun] public
open Ord.[Rel] public
open Ord.[Fun|Fun] public
open Ord.[Rel|Fun] public
