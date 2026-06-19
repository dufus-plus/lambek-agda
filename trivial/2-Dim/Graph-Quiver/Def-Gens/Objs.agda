open import 0-Dim.!quali
import 1-Dim.Graph.Def-Gens.Objs as Graph
open import 2-Dim.Quiver.Def-Types.Obj
open import 2-Dim.Quiver.Def-Types-pub.Obj

module 2-Dim.Quiver.Def-Gens.Objs where

Unit : [Obj]
Unit .Ob = Any.Unit
Unit .Hom _ = Graph.Unit

Void : [Obj]
Void .Ob = Any.Void
Void .Hom ()

module _ (AB @(A × B) : [2×] [Obj]) where
  Prod2 : [Obj]
  Prod2 .Ob = Any.Prod2 (A .Ob × B .Ob)
  Prod2 .Hom ((a1 × b1) ~ (a2 × b2)) = Graph.Prod2 (A .Hom (a1 ~ a2) × B .Hom (b1 ~ b2))

module _ (AB @(A + B) : [2×] [Obj]) where
  Summ2 : [Obj]
  Summ2 .Ob = Any.Summ2 (A .Ob × B .Ob)
  Summ2 .Hom (↑₁ a1 ~ ↑₁ a2) = A .Hom (a1 ~ a2)
  Summ2 .Hom (↑₁ a1 ~ ↑₂ b2) = Graph.Void
  Summ2 .Hom (↑₂ b1 ~ ↑₁ a2) = Graph.Void
  Summ2 .Hom (↑₂ b1 ~ ↑₂ b2) = B .Hom (b1 ~ b2)
