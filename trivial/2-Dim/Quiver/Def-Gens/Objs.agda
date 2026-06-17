open import 0-Dim.!quali
import 1-Dim.Set.Def-Gens.Objs as Set
open import 2-Dim.Quiver.Def-Types.Obj
open import 2-Dim.Quiver.Def-Types-pub.Obj

module 2-Dim.Quiver.Def-Gens.Objs where

Unit : [Obj]
Unit .Ob = Any.Unit
Unit .Hom _ = Set.Unit

Void : [Obj]
Void .Ob = Any.Void
Void .Hom ()

module _ (AB @(A × B) : [2×] [Obj]) where
  Prod : [Obj]
  Prod .Ob = Any.Prod2 (A .Ob × B .Ob)
  Prod .Hom ((a1 × b1) ~ (a2 × b2)) = Set.Prod2 (A .Hom (a1 ~ a2) × B .Hom (b1 ~ b2))

module _ (AB @(A + B) : [2×] [Obj]) where
  Summ : [Obj]
  Summ .Ob = Any.Summ2 (A .Ob × B .Ob)
  Summ .Hom (↑₁ a1 ~ ↑₁ a2) = A .Hom (a1 ~ a2)
  Summ .Hom (↑₁ a1 ~ ↑₂ b2) = Set.Void
  Summ .Hom (↑₂ b1 ~ ↑₁ a2) = Set.Void
  Summ .Hom (↑₂ b1 ~ ↑₂ b2) = B .Hom (b1 ~ b2)
