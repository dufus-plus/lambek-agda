open import 0-Dim.Prelude.Agda
open import 0-Dim.Prelude.Tilda
open import 0-Dim.Prelude.Cross

module 0-Dim.Prelude.Rel where

-- the unit relation
data [≡] (Arg : [Any]) : (2arg : [2~] Arg) → [Any] where
  ≡ : (arg : Arg) → [≡] Arg (arg ~ arg)

module ≡ where

  module _ {Arg : [Any]}
           {arg : [1~] Arg} where
    refl : [≡] Arg (arg ~ arg)
    refl = (≡ _)

  module _ {Arg : [Any]}
           {2arg @(a1 ~ a2) : [2~] Arg} where
    symm : [≡] Arg (a2 ~ a1) → [≡] Arg (a1 ~ a2)
    symm (≡ _) = (≡ _)

  module _ {Arg : [Any]}
           {3arg @(a1 ~ a2 ~ a3) : [3~] Arg} where
    tran : [≡] Arg (a1 ~ a2) [×] [≡] Arg (a2 ~ a3) → [≡] Arg (a1 ~ a3)
    tran (≡ _ × ≡ _) = (≡ _)

  module _ {AB @(A > B) : [2~] [Any]}
           (f : A → B)
           {2a @(a1 ~ a2) : [2~] A} where
    cong : [≡] A (a1 ~ a2) → [≡] B (f a1 ~ f a2)
    cong (≡ _) = (≡ _)

-- composition of relations
module _ {[-] [+] : [Any]} {[0] : [Any]} where
  module _ ([₋~₀] : ([-] [~] [0]) → [Any]) ([₀~₊] : ([0] [~] [+]) → [Any])
           (2a @(a- ~ a+): [-] [~] [+]) where
    record _[∙]_ : [Any] where
      constructor _∙_
      field {₀} : [0]
      field ₋~₀ : [₋~₀] (a- ~ ₀)
      field ₀~₊ : [₀~₊] (₀ ~ a+)
    open _[∙]_ public

-- reverse relation
module _ {AB @(A ~ B) : [2~] [Any]} (Rba : (B [~] A) → [Any]) where
  [-] : (ab : A [~] B) → [Any]
  [-] (a ~ b) = Rba (b ~ a)

-- path relation of the given one
module _ (A : [Any]) (R : [2~] A → [Any]) where
  [Path] : (nat : [Nat]) → ([2~] A → [Any])
  [Path] 0! = [≡] A
  [Path] (1!+ n) = R [∙] [Path] n

  [nPath] : [2~] A → [Any]
  [nPath] 2a = [Nat] [×d] λ n → [Path] n 2a

module Path where
  module _ (A : [Any]) (R : [2~] A → [Any]) where
    One : (2a : [2~] A) → R 2a → [Path] A R 1! 2a
    One (a1 ~ a2) r = r ∙ ≡ a2

    Id : (a : A) → [Path] A R 0! (a ~ a)
    Id a = ≡ a

    Mu :
      (3a @(a1 ~ a2 ~ a3) : [3~] A)
      (2n @(n12 × n23) : [2×] [Nat])
      (2p @(p12 × p23) : [Path] A R n12 (a1 ~ a2) [×] [Path] A R n23 (a2 ~ a3))
      → [Path] A R (Nat.Summ2 n12 n23) (a1 ~ a3)
    Mu _ (0! × n23) (≡ _ × p23) = p23
    Mu _ (1!+ n12 × n23) ((p10 ∙ p02) × p23) = p10 ∙ (Mu _ (n12 × n23) (p02 × p23))

    Snoc :
      (3a @(a1 ~ a2 ~ a3) : [3~] A)
      (n : [Nat])
      (p : [Path] A R n (a1 ~ a2))
      (r : R (a2 ~ a3))
      → [Path] A R (1!+ n) (a1 ~ a3)
    Snoc _ 0! (≡ _) r = One _ r
    Snoc _ (1!+ n) (r0 ∙ p) r = r0 ∙ (Snoc _ n p r)

  module _ (A : [Any]) (R : [2~] A → [Any]) where
    Rev :
      (2a @(a1 ~ a2) : [2~] A)
      (n : [Nat])
      (p : [Path] A R n (a1 ~ a2) )
      → [Path] A ([-] R) n (a2 ~ a1)
    Rev _ 0! p = ≡.symm p
    Rev _ (1!+ n) (r ∙ p) = Snoc A ([-] R) _ n (Rev _ n p) r

  module _ (A : [Any]) (2R @(R1 > R2) : [2~] ([2~] A → [Any])) where
    Map :
      (f : ∀ 2a → R1 2a → R2 2a)
      (2a : [2~] A)
      (n : [Nat])
      (p : [Path] A R1 n 2a)
      → [Path] A R2 n 2a
    Map f _ 0! p = p
    Map f _ (1!+ n) (r ∙ p) = f _ r ∙ Map f _ n p

module nPath where
  module _ (A : [Any]) (R : [2~] A → [Any]) where
    One : (2a : [2~] A) → R 2a → [nPath] A R 2a
    One 2a r = 1! ×d Path.One A R 2a r

    Id : (a : A) → [nPath] A R (a ~ a)
    Id a = 0! ×d Path.Id A R a

    Mu :
      (3a @(a1 ~ a2 ~ a3) : [3~] A) →
      (2p @(p12 × p23) : [nPath] A R (a1 ~ a2) [×] [nPath] A R (a2 ~ a3))
      → [nPath] A R (a1 ~ a3)
    Mu _ ((n12 ×d p12) × (n23 ×d p23)) =
      (Nat.Summ2 n12 n23) ×d Path.Mu A R _ (n12 × n23) (p12 × p23)

    Snoc :
      (3a @(a1 ~ a2 ~ a3) : [3~] A)
      (p : [nPath] A R (a1 ~ a2))
      (r : R (a2 ~ a3))
      → [nPath] A R (a1 ~ a3)
    Snoc _ (n ×d p) r = (1!+ n) ×d Path.Snoc A R _ n p r

  module _ (A : [Any]) (R : [2~] A → [Any]) where
    Rev :
      (2a @(a1 ~ a2) : [2~] A)
      (p  : [nPath] A R (a1 ~ a2) )
      → [nPath] A ([-] R) (a2 ~ a1)
    Rev _ (n ×d p) = n ×d Path.Rev A R _ n p

  module _ (A : [Any]) (2R @(R1 > R2) : [2~] ([2~] A → [Any])) where
    Map :
      (f : ∀ 2a → R1 2a → R2 2a)
      (2a : [2~] A)
      (p : [nPath] A R1 2a)
      → [nPath] A R2 2a
    Map f 2a (n ×d p) = n ×d Path.Map A 2R f 2a n p
