open import 0-Dim.Prelude.!all
open import 0-Dim.Any.Def-Types

-- instances generators on [Any]

module 0-Dim.Any.Def-Gens where

Void : [Any]
Void = [⊥]

Unit : [Any]
Unit = [!]

module _ (AB @(A × B) : [Any] [×] [Any]) where
  Prod2 : [Any]
  Prod2 = A [×] B

  Summ2 : [Any]
  Summ2 = A [+] B

module _ (IA @(I > A) : [Any] [~] [Any]) where
  Pow : [Any]
  Pow = I → A

module _ (IA @(I , A) : [Any] [×] [Any]) where
  CoPow : [Any]
  CoPow = I [×] A

module _ (IA @(I ~d A) : [Any] [~d] (λ I → I → [Any])) where
  ProdI : [Any]
  ProdI = (i : I) → A i

module _ (IA @(I ×d A) : [Any] [×d] (λ I → I → [Any])) where
  SummI : [Any]
  SummI = I [×d] A

module _ (A : [Any]) where
  module Void where
    Init : Void → A
    Init ()
  module Unit where
    Term : A → Unit
    Term _ = !

module Prod2 where
  module _ (AB @(A × B) : [Any] [×] [Any]) where
    Prj1 : [Fun] (Prod2 (A × B) > A)
    Prj1 = ↓₁
    Prj2 : [Fun] (Prod2 (A × B) > B)
    Prj2 = ↓₂
  module _ (X : [Any]) where
    Diag : [Fun] (X > Prod2 (X × X))
    Diag x = x × x

module Summ2 where
  module _ (AB @(A + B) : [Any] [×] [Any]) where
    Inj1 : [Fun] (A > Summ2 (A + B))
    Inj1 = ↑₁
    Inj2 : [Fun] (B > Summ2 (A + B))
    Inj2 = ↑₂
  module _ (X : [Any]) where
    Glue : [Fun] (Summ2 (X + X) > X)
    Glue (↑₁ x) = x
    Glue (↑₂ x) = x

module Pow (IA @(I > A) : [Any] [~] [Any]) where
  Prj : (i : I) → [Fun] (Pow (I > A) > A)
  Prj i p = p i
  Diag : [Fun] (A > Pow (I > A))
  Diag a i = a

module CoPow (IA @(I , A) : [Any] [×] [Any]) where
  Inj : (i : I) → [Fun] (A > CoPow IA)
  Inj i a = i , a
  Glue : [Fun] (CoPow IA > A)
  Glue (i , a) = a

module ProdI where
  module _ (IA @(I ~d A) : [Any] [~d] (λ I → I → [Any])) where
    Prj : (i : I) → [Fun] (ProdI IA > A i)
    Prj i p = p i
  module _ (IA @(I > A) : [Any] [~] [Any]) where
    Diag : [Fun] (A > ProdI (I ~d λ _ → A))
    Diag a i = a

module SummI where
  module _ (IA @(I ×d A) : [Any] [×d] (λ I → I → [Any])) where
    Inj : (i : I) → [Fun] (A i > SummI IA)
    Inj i a = i ×d a
  module _ (IA @(I × A) : [Any] [×] [Any]) where
    Glue : [Fun] (SummI (I ×d λ _ → A) > A)
    Glue (i ×d a) = a

Const : (AB @(A ~ B) : [2~] [Any]) → B → (A → B)
Const _ b a = b
