open import 0-Dim-qua
import 1-Dim.Set.Def-Gens.Objs as Set
open import 2-Dim.Quiver.Def-Types.Ob
open import 2-Dim.Quiver.Def-Types-pub.Ob

module 2-Dim.Quiver.Def-Gens.Objs where

Unit : [Ob]
Unit .Ob = Any.Unit
Unit .Hom _ = Set.Unit

Void : [Ob]
Void .Ob = Any.Void
Void .Hom ()

module _ (AB @(A × B) : [Ob] [×] [Ob]) where
  Prod : [Ob]
  Prod .Ob = Any.Prod2 (A .Ob × B .Ob)
  Prod .Hom ((a1 × b1) ~ (a2 × b2)) = Set.Prod2 (A .Hom (a1 ~ a2) × B .Hom (b1 ~ b2))

module _ (AB @(A + B) : [Ob] [×] [Ob]) where
  Summ : [Ob]
  Summ .Ob = Any.Summ2 (A .Ob × B .Ob)
  Summ .Hom (↑₁ a1 ~ ↑₁ a2) = A .Hom (a1 ~ a2)
  Summ .Hom (↑₁ a1 ~ ↑₂ b2) = Set.Void
  Summ .Hom (↑₂ b1 ~ ↑₁ a2) = Set.Void
  Summ .Hom (↑₂ b1 ~ ↑₂ b2) = B .Hom (b1 ~ b2)
