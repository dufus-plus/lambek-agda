import =Curry=

module =Bishop-omegaType= where

open =Curry=

-- components of the double category of Orders
module ωSet where

  -- objects of category of Orders
  record [Ob] : ωType₁ where
    constructor !
    field [El] : ωType
    field [To] : (el el' : [El]) → ωType
    field Refl : ∀ el0 → [To] el0 el0
    field Symm : ∀ {el1 el2} → (to21 : [To] el2 el1) → [To] el1 el2
    field Tran : ∀ {el1 el2 el3} → (to12 : [To] el1 el2) → (to23 : [To] el2 el3) → [To] el1 el3
  open [Ob] public

  -- function morphisms
  record [Fun] (A B : [Ob]): ωType where
    constructor !
    field fEl : A .[El] → B .[El]
    field fTo : ∀ {el1 el2} → A .[To] el1 el2 → B .[To] (fEl el1) (fEl el2)
  open [Fun] public

  -- relation morphisms
  record [Rel] (A B : [Ob]): ωType₁ where
    constructor !
    field [rEl] : A .[El] → B .[El] → ωType
    field LTran : ∀ {ael ael' bel} → A .[To] ael ael' → [rEl] ael' bel → [rEl] ael bel
    field RTran : ∀ {ael bel bel'} → [rEl] ael bel → B .[To] bel bel' → [rEl] ael bel'
  open [Rel] public

  module _ {A B : [Ob]} where
    [FunTo] : (f g : [Fun] A B) → ωType
    [FunTo] f g = ∀ a → B .[To] (f .fEl a) (g .fEl a)
    [RelTo] : (R R' : [Rel] A B) → ωType
    [RelTo] R R' = ∀ {a b} → R .[rEl] a b → R' .[rEl] a b

  module _ (A : [Ob]) where
    Opp : [Ob]
    Opp .[El] = A .[El]
    Opp .[To] a b = A .[To] b a
    Opp .Refl = A .Refl
    Opp .Symm ato21 = A .Symm ato21
    Opp .Tran ato12 ato23 = A .Tran ato23 ato12

  module _ (A B : [Ob]) where
    Funᵒ : [Ob]
    Funᵒ .[El] = [Fun] A B
    Funᵒ .[To] f g = [FunTo] f g
    Funᵒ .Refl _ a = B .Refl _
    Funᵒ .Symm fto21 a = B .Symm (fto21 a)
    Funᵒ .Tran fto12 fto23 a = B .Tran (fto12 a) (fto23 a)
    -- Relᵒ : [Ob]
    -- Relᵒ .[El] = [Rel] A B
    -- Relᵒ .[To] R R' = [RelTo] R R'
    -- Relᵒ .Refl R a b = ⑴
    -- Relᵒ .Tran R1 R2 R3 rto12 rto23 a b = rto12 a b ∘ rto23 a b

  module _ (A : [Ob]) where
    Fun-Id : [Fun] A A
    Fun-Id = record where
      fEl = ω⑴
      fTo = ω⑴
    Rel-Id : [Rel] A A
    Rel-Id = record where
      [rEl] = A .[To]
      LTran = A .Tran
      RTran = A .Tran

  module _ {A B C : [Ob]} where
    Fun-Mu : [Fun] A B → [Fun] B C → [Fun] A C
    Fun-Mu fab fbc .fEl = fab .fEl ω∘ fbc .fEl
    Fun-Mu fab fbc .fTo = fab .fTo ω∘ fbc .fTo
    Rel-Mu : [Rel] A B → [Rel] B C → [Rel] A C
    Rel-Mu Rab Rbc .[rEl] = (Rab .[rEl]) ω[∙] (Rbc .[rEl])
    Rel-Mu Rab Rbc .LTran aeq12 (rab ∙ rbc) = (Rab .LTran aeq12 rab) ∙ rbc
    Rel-Mu Rab Rbc .RTran (rab ∙ rbc) ceq12 = rab ∙ (Rbc .RTran rbc ceq12)

  -- representable and corepresentable relation
  module _ {A B : [Ob]} where
    Rep+ : [Fun] A B → [Rel] A B
    Rep+ f .[rEl] a b = B .[To] (f .fEl a) b
    Rep+ f .LTran ato12 rab = B .Tran (f .fTo ato12) rab
    Rep+ f .RTran rab bto12 = B .Tran rab bto12

    Rep- : [Fun] A B → [Rel] B A
    Rep- f .[rEl] b a = B .[To] b (f .fEl a)
    Rep- f .LTran bto12 rab = B .Tran bto12 rab
    Rep- f .RTran rab ato12 = B .Tran rab (f .fTo ato12)

  module _ (A B : [Ob]) where
    Const : B .[El] → [Fun] A B
    Const b .fEl = Type.ωConst (A .[El]) (B .[El]) b
    Const b .fTo _ = B .Refl b

  module _ {A11 A12 A21 A22 : [Ob]} where
    Rel-Up : [Fun] A11 A21 → [Fun] A12 A22 → [Rel] A21 A22 → [Rel] A11 A12
    Rel-Up v1 v2 h .[rEl] a11 a12 = h .[rEl] (v1 .fEl a11) (v2 .fEl a12)
    Rel-Up v1 v2 h .LTran a11to r = h .LTran (v1 .fTo a11to) r
    Rel-Up v1 v2 h .RTran r a12to = h .RTran r (v2 .fTo a12to)
    module _ (v1 : [Fun] A11 A21)(v2 : [Fun] A12 A22)
             (h1 : [Fun] A11 A12)(h2 : [Fun] A21 A22) where
      record [Fun|Fun] : ωType where
        constructor ↑
        field ↓ : [FunTo] (Fun-Mu v1 h2) (Fun-Mu h1 v2)
      open [Fun|Fun] public
    module _ (v1 : [Fun] A11 A21)(v2 : [Fun] A12 A22)
             (h1 : [Rel] A11 A12)(h2 : [Rel] A21 A22) where
      record [Rel|Fun] : ωType where
        constructor ↑
        field ↓ : [RelTo] h1 (Rel-Up v1 v2 h2)
      open [Rel|Fun] public

  module _ {A B} (f : [Fun] A B) where
    Rel-Id|Fun : [Rel|Fun] f f (Rel-Id A) (Rel-Id B)
    Rel-Id|Fun .↓ = f .fTo

  -- just (E)ndo-(F)unctors on (O)rders
  record [EFO] : ωType₁ where
    constructor !
    field f-el : [Ob] → [Ob]
    field f-Fun : ∀ {A B} → [Fun] A B → [Fun] (f-el A) (f-el B)
    field f-Rel : ∀ {A B} → [Rel] A B → [Rel] (f-el A) (f-el B)
    field
     f-Rel|Fun :
      ∀ {A11 A12 A21 A22} →
        {v1 : [Fun] A11 A21} {v2 : [Fun] A12 A22} {h1 : [Rel] A11 A12} {h2 : [Rel] A21 A22} →
        [Rel|Fun] v1 v2 h1 h2 →
        [Rel|Fun] (f-Fun v1) (f-Fun v2) (f-Rel h1) (f-Rel h2)
    -- field fun-id
    -- field fun-mu
    field rel-id-to : ∀ {A} → [RelTo] (Rel-Id (f-el A)) (f-Rel (Rel-Id A))
    field rel-id-fr : ∀ {A} → [RelTo] (f-Rel (Rel-Id A)) (Rel-Id (f-el A))
  open [EFO] public
--

-- make record fields visible outside w/o module prefix
[ωSet] = ωSet.[Ob]
open ωSet.[Ob] public
open ωSet.[Fun] public
open ωSet.[Rel] public
open ωSet.[Fun|Fun] public
open ωSet.[Rel|Fun] public
