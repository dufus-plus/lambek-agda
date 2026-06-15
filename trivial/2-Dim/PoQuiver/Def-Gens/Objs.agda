open import 0-Dim-qua
import 1-Dim.PoSet.Def-Gens.Objs as PoSet
open import 2-Dim.PoQuiver.Def-Types.Ob
open import 2-Dim.PoQuiver.Def-Types-pub.Ob

module 2-Dim.PoQuiver.Def-Gens.Objs where

Unit : [Ob]
Unit .Ob = Any.Unit
Unit .Hom _ = PoSet.Unit

Void : [Ob]
Void .Ob = Any.Void
Void .Hom ()

module _ (AB @(A × B) : [Ob] [×] [Ob]) where
  Prod : [Ob]
  Prod .Ob = Any.Prod2 (A .Ob × B .Ob)
  Prod .Hom ((a1 × b1) ~ (a2 × b2)) = PoSet.Prod2 (A .Hom (a1 ~ a2) × B .Hom (b1 ~ b2))

module _ (AB @(A + B) : [Ob] [×] [Ob]) where
  Summ : [Ob]
  Summ .Ob = Any.Summ2 (A .Ob × B .Ob)
  Summ .Hom (↑₁ a1 ~ ↑₁ a2) = A .Hom (a1 ~ a2)
  Summ .Hom (↑₁ a1 ~ ↑₂ b2) = PoSet.Void
  Summ .Hom (↑₂ b1 ~ ↑₁ a2) = PoSet.Void
  Summ .Hom (↑₂ b1 ~ ↑₂ b2) = B .Hom (b1 ~ b2)
