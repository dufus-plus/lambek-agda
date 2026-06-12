import =Curry=
import =Bishop=

--
-- the initial order
--
module =Void= where

open =Curry=
open =Bishop=

module Void-Encoding where
  [%Ob] = Ord.[%Ob]
  [Ob] = Ord.[Ob]
  [Fun] = Ord.[Fun]
  [Rel] = Ord.[Rel]

  -- limit of identity functor
  module _ (% : [%Ob]) where
    Lim%-El = 1+ (% .El) ⊔ 1+ (% .To)
    record [Lim] : Type Lim%-El where
      constructor ! 
      field lOb : (X : [Ob] %) → X .[El]
      field lRel : (A B : [Ob] %) → (R : [Rel] (% .To) A B) → R .[rEl] (lOb A) (lOb B)
    open [Lim] public
    
    Lim%-To = 1+ (% .El) ⊔ 1+ (% .To)
    Lim-To : (l1 l2 : [Lim]) → Type Lim%-To
    Lim-To l1 l2 = (X : [Ob] %) → X .[To] (l1 .lOb X) (l2 .lOb X)
    
    Lim% : Ord.[%Ob]
    Lim% .El = Lim%-El
    Lim% .To = Lim%-To

    Lim : Ord.[Ob] Lim%
    Lim .[El] = [Lim]
    Lim .[To] = Lim-To
    Lim .Refl l X = X .Refl (l .lOb X)
    Lim .Tran _ _ _ feq12 feq23 X = X .Tran _ _ _ (feq12 X) (feq23 X)

    cone-Ob-El : (X : [Ob] %) → [Lim] → X .[El]
    cone-Ob-El X lim = lim .lOb X 

    cone-Ob : (X : [Ob] %) → Ord.[Fun] Lim X
    cone-Ob X .fEl = cone-Ob-El X
    cone-Ob X .fTo _ _ limeq12 = limeq12 X

  module _ {%A %B : [%Ob]} {%R : [Level]}
           {A : [Ob] %A} {B : [Ob] %B} (R : [Rel] %R A B) where
    -- cone-Rel : Ord.[Rel|Fun] (cone-Ob _ A) (cone-Ob _ B) (Ord.Rel-Id Lim ?) R
    -- cone-Rel .↓ _ l2 lto = R .LTran _ _ _ (lto A) (l2 .lRel _ _ R)
    -- cone-Rel .↓ l1 _ lto = R .RTran _ _ _ (l1 .lRel _ _ R) (lto B)

--   Lim-To-fw : [FunTo] (Ord.Fun-Id Limᵒ) (Limᵒ-Ob Limᵒ)
--   Lim-To-fw l X = l .lRel _ _ (Rep- (Limᵒ-Ob X)) 
--   Lim-To-bw : [FunTo] (Limᵒ-Ob Limᵒ) (Ord.Fun-Id Limᵒ)
--   Lim-To-bw l X = l .lRel _ _ (Rep+ (Limᵒ-Ob X)) 

-- --
-- open Void-Encoding.[Lim] public
-- [Void] = Void-Encoding.[Lim]
-- Voidᵒ = Void-Encoding.Limᵒ 
-- recur = Void-Encoding.Lim-Ob















