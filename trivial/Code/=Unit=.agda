import =Curry=
import =Bishop=

--
-- initial order with element, also terminal one
--
module =Unit= where

open =Curry=
open =Bishop=

module Unit-Encoding where

  record [Ob] : Type where
    constructor !
    field It : Ord.[Ob]
    open Ord.[Ob] It public
    field Is : It .[El]
  open [Ob] public 

  record [Fun] (A B : [Ob]) : Type where
    constructor !
    field fIt : Ord.[Fun] (A .It) (B. It)
    open Ord.[Fun] fIt public
    field fIs-fw : B .[To] (fIt .fEl (A .Is)) (B .Is)
    field fIs-bw : B .[To] (B .Is) (fIt .fEl (A .Is))
  open [Fun] public

  record [Rel] (A B : [Ob]) : Type where
    constructor !
    field rIt : Ord.[Rel] (A .It) (B. It)
    open Ord.[Rel] rIt public
    field rIs : rIt .[rEl] (A .Is) (B .Is)
  open [Rel] public

  module _ {A B : [Ob]} where
    Rep+ : [Fun] A B → [Rel] A B
    Rep+ f .rIt = Ord.Rep+ (f .fIt)
    Rep+ f .rIs = f .fIs-fw 

    Rep- : [Fun] A B → [Rel] B A
    Rep- f .rIt = Ord.Rep- (f .fIt)
    Rep- f .rIs = f .fIs-bw 

  module _ (A B : [Ob]) where
    Const : [Fun] A B
    Const .fIt = Ord.Const (A .It) (B .It) (B .Is)
    Const .fIs-fw = B .Refl (B .Is)
    Const .fIs-bw = B .Refl (B .Is)

  -- limit of identity
  record [Lim] : Type where
    constructor ! 
    field lOb : (X : [Ob]) → X .[El]
    field lRel : (A B : [Ob]) → (R : [Rel] A B) → R .[rEl] (lOb A) (lOb B)
  open [Lim] public

  Limᵒ : Ord.[Ob]
  Limᵒ .[El] = [Lim]
  Limᵒ .[To] l1 l2 = (X : [Ob]) → X .[To] (l1 .lOb X) (l2 .lOb X)
  Limᵒ .Refl l X = X .Refl (l .lOb X)
  Limᵒ .Tran _ _ _ feq12 feq23 X = X .Tran _ _ _ (feq12 X) (feq23 X)

  module Init where
    Lim-Ob : (X : [Ob]) → [Lim] → X .[El]
    Lim-Ob X lim = lim .lOb X 

    Limᵒ-Ob : (X : [Ob]) → Ord.[Fun] Limᵒ (X .It)
    Limᵒ-Ob X .fEl = Lim-Ob X
    Limᵒ-Ob X .fTo _ _ limeq12 = limeq12 X

    module _ {A B : [Ob]} (R : [Rel] A B) where
      Limᵒ-Rel : Ord.[Rel|Fun] (Limᵒ-Ob A) (Limᵒ-Ob B) (Ord.Rel-Id Limᵒ) (R .rIt)
      -- Limᵒ-Rel .↓ _ l2 lto = R .LTran _ _ _ (lto A) (l2 .lRel _ _ R)
      Limᵒ-Rel .↓ l1 _ lto = R .RTran _ _ _ (l1 .lRel _ _ R) (lto B)

    -- algebra structure on [Lim]
    Limᵃ : [Ob]
    Limᵃ .It = Limᵒ 
    Limᵃ .Is .lOb X = X .Is
    Limᵃ .Is .lRel A B R = R .rIs

    Limᵃ-Ob : (X : [Ob]) → [Fun] Limᵃ X
    Limᵃ-Ob X .fIt = Limᵒ-Ob X
    Limᵃ-Ob X .fIs-fw = X .Refl _
    Limᵃ-Ob X .fIs-bw = X .Refl _

    Lim-To-fw : Ord.[FunTo] (Ord.Fun-Id Limᵒ) (Limᵒ-Ob Limᵃ)
    Lim-To-fw l X = l .lRel _ _ (Rep- (Limᵃ-Ob X)) 
    Lim-To-bw : Ord.[FunTo] (Limᵒ-Ob Limᵃ) (Ord.Fun-Id Limᵒ)
    Lim-To-bw l X = l .lRel _ _ (Rep+ (Limᵃ-Ob X)) 

    Lim-term-fw : ∀ l → Limᵒ .[To] l (Limᵃ .Is)
    Lim-term-fw l X = l .lRel _ _ (Rep- (Const X X))
    Lim-term-bw : ∀ l → Limᵒ .[To] (Limᵃ .Is) l
    Lim-term-bw l X = l .lRel _ _ (Rep+ (Const X X))

--
open Unit-Encoding.[Lim] public
[Unit] = Unit-Encoding.[Lim]
Unitᵒ = Unit-Encoding.Limᵒ 
recur = Unit-Encoding.Lim-Ob