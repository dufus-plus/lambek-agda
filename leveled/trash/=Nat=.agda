import =Curry=

--
-- the initial order
--
module =Nat= where

open =Curry=

module Nat-Encoding where
  
  record [Ob] (ℓ : [Level]) : Type (1+ ℓ) where
    constructor !
    field [] : Type ℓ 
    field MkZ : [] 
    field MkS : [] → []
  open [Ob] public

  record [Lim] (ℓ : [Level]) : Type (1+ ℓ) where
    constructor !
    field lOb : (X : [Ob] ℓ) → X .[]
  open [Lim] public

  module _ (ℓ : [Level]) where

    Lim-MkZ : [Lim] ℓ
    Lim-MkZ .lOb X = X .MkZ

    Lim-MkS : [Lim] ℓ → [Lim] ℓ
    Lim-MkS l .lOb X = X .MkS (l .lOb X)

    Lim : [Ob] (1+ ℓ)
    Lim .[] = [Lim] ℓ
    Lim .MkZ = Lim-MkZ
    Lim .MkS = Lim-MkS

    Lim-add : [Lim] (1+ ℓ) → [Lim] ℓ → [Lim] ℓ
    Lim-add l1 l2 = l1 .lOb (! _ l2 Lim-MkS) 

    Lim-mul : [Lim] (1+ ℓ) → [Lim] (1+ ℓ) → [Lim] ℓ
    Lim-mul l1 l2 = l1 .lOb (! _ Lim-MkZ (Lim-add l2)) 
  --

  [Nat] = ∀ ℓ → [Lim] ℓ
  
  Nat-MkZ : [Nat]
  Nat-MkZ ℓ = Lim-MkZ ℓ

  Nat-MkS : [Nat] → [Nat]
  Nat-MkS n ℓ = Lim-MkS ℓ (n ℓ)

  Nat-add : [Nat] → [Nat] → [Nat]
  Nat-add n m ℓ = Lim-add ℓ (n (1+ ℓ)) (m ℓ)

  Nat-mul : [Nat] → [Nat] → [Nat]
  Nat-mul n m ℓ = Lim-mul ℓ (n (1+ ℓ)) (m (1+ ℓ))