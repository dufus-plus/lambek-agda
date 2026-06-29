import =Curry=
import =Bishop=

--
-- initial algebras of endofunctors
--
module =Lambek= where

open =Curry=
open =Bishop=

module Alg (E : Ord.[EFO]) where

  open Ord.[EFO] E

  record [Ob] : Type where
    constructor !
    field It : Ord.[Ob]
    open Ord.[Ob] It public
    field Is : Ord.[Fun] (f-el It) It
    open Ord.[Fun] Is public
  open [Ob] public

  record [Fun] (A B : [Ob]) : Type where
    constructor !
    field fIt : Ord.[Fun] (A .It) (B. It)
    open Ord.[Fun] fIt public
    field fIs : Ord.[Fun|Fun] (A .Is) (B .Is) (f-Fun fIt) fIt
  open [Fun] public

  record [Rel] (A B : [Ob]) : Type where
    constructor !
    field rIt : Ord.[Rel] (A .It) (B. It)
    open Ord.[Rel] rIt public
    field rIs : Ord.[Rel|Fun] (A .Is) (B .Is) (f-Rel rIt) rIt
  open [Rel] public

  -- limit of all
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

  Lim-Ob : (X : [Ob]) → [Lim] → X .[El]
  Lim-Ob X lim = lim .lOb X

  Limᵒ-Ob : (X : [Ob]) → Ord.[Fun] Limᵒ (X .It)
  Limᵒ-Ob X .fEl = Lim-Ob X
  Limᵒ-Ob X .fTo _ _ limeq12 = limeq12 X

  module _ {A B : [Ob]} (R : [Rel] A B) where
    Lim-Rel : Ord.[Rel|Fun] (Limᵒ-Ob A) (Limᵒ-Ob B) (Ord.Rel-Id Limᵒ) (R .rIt)
    -- Lim-Rel .↓ _ l2 lto = R .LTran _ _ _ (lto A) (l2 .lRel _ _ R)
    Lim-Rel .↓ l1 _ lto = R .RTran _ _ _ (l1 .lRel _ _ R) (lto B)

  encode : f-el Fixᵒ .[El] → [Fix]
  encode ffix .lOb X = X .fEl ((f-Fun (recurᵒ X)) .fEl ffix)
  encode ffix .lRel A B R =
    R .rIs .↓ _ _
      ((f-Rel|Fun (recur-rel R)) .↓ _ _ (rel-id-to _ _ (f-el Fixᵒ .Refl ffix)))

  -- encodeᵒ : Ord.[Fun] (F .Ob Fixᵒ) Fixᵒ
  -- encodeᵒ .El = encode
  -- encodeᵒ .To ffix1 ffix2 fto12 X = {!   !}
  --   where
  --     qq : _
  --     qq = X .ris .To _ _
  --       (F .Rel|Fun (Ord.Rel-Id|Fun (recurᵒ X))) .↓ _ _ (F .rel-id-to _ _ fto12)

  -- Fixᵃ : [Ob] -- algebra
  -- Fixᵃ .It = Fixᵒ
  -- Fixᵃ .Is = --

  -- recurᵃ : (X : [Ob]) → [Fun] Fixᵃ X

-- decode : ∀ {F} → coAlg F (Fix F)
-- decode {F} = recur (F / encode)
