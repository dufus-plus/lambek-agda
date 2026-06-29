import =Curry=
import =Bishop=

--
-- the initial order
--
module =Void= where

open =Curry=
open =Bishop=

module Void-Encoding where

  [Ob] = [Set]
  [Fun] = Set.[Fun]
  [Rel] = Set.[Rel]

  -- limit of identity
  record [Lim] : Type where
    constructor ! 
    field lOb : (X : [Ob]) → X .[El]
    field lRel : (A B : [Ob]) → (R : [Rel] A B) → R .[rEl] (lOb A) (lOb B)
  open [Lim] public

  Limᵒ : [Set]
  Limᵒ .[El] = [Lim]
  Limᵒ .[To] l1 l2 = (X : [Ob]) → X .[To] (l1 .lOb X) (l2 .lOb X)
  Limᵒ .Refl l X = X .Refl (l .lOb X)
  Limᵒ .Symm _ _ lto21 X = X .Symm _ _ (lto21 X)
  Limᵒ .Tran _ _ _ lto12 lto23 X = X .Tran _ _ _ (lto12 X) (lto23 X)

  Lim-Ob : (X : [Ob]) → [Lim] → X .[El]
  Lim-Ob X lim = lim .lOb X 

  Limᵒ-Ob : (X : [Ob]) → Set.[Fun] Limᵒ X
  Limᵒ-Ob X .fEl = Lim-Ob X
  Limᵒ-Ob X .fTo _ _ limeq12 = limeq12 X

  module _ {A B : [Ob]} (R : [Rel] A B) where
    Limᵒ-Rel : Set.[Rel|Fun] (Limᵒ-Ob A) (Limᵒ-Ob B) (Set.Rel-Id Limᵒ) R
    -- Limᵒ-Rel .↓ _ l2 lto = R .LTran _ _ _ (lto A) (l2 .lRel _ _ R)
    Limᵒ-Rel .↓ l1 _ lto = R .RTran _ _ _ (l1 .lRel _ _ R) (lto B)

  Lim-To-fw : Set.Fun-[To] (Set.Fun-Id Limᵒ) (Limᵒ-Ob Limᵒ)
  Lim-To-fw l X = l .lRel _ _ (Set.Rep- (Limᵒ-Ob X)) 
  Lim-To-bw : Set.Fun-[To] (Limᵒ-Ob Limᵒ) (Set.Fun-Id Limᵒ)
  Lim-To-bw l X = l .lRel _ _ (Set.Rep+ (Limᵒ-Ob X)) 

--
open Void-Encoding.[Lim] public
[Void] = Void-Encoding.[Lim]
Voidᵒ = Void-Encoding.Limᵒ 
recur = Void-Encoding.Lim-Ob
