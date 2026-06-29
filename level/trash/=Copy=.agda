import =Curry=

--
-- the initial order
--
module =Copy= where

open =Curry=

module Copy-Encoding (A : Type 0%) where
  
  record [Ob] (ℓ : [Level]) : Type (1+ ℓ) where
    constructor !
    field [] : Type ℓ 
    field Mk : A → [] 
  open [Ob] public

  record [Lim] (ℓ : [Level]) : Type (1+ ℓ) where
    constructor !
    field lOb : (X : [Ob] ℓ) → X .[]
  open [Lim] public

  module _ (ℓ : [Level]) where

    encode : A → [Lim] ℓ
    encode A .lOb X = X .Mk A

    Lim : [Ob] (1+ ℓ)
    Lim .[] = [Lim] ℓ
    Lim .Mk = encode

  decode : [Lim] 0% → A
  decode l₀ = l₀ .lOb (! _ (λ (a : A) → a))
  


