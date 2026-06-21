open import 0-Dim.!quali
import 1-Dim.PoSet.Def-Gens.Objs as PoSet
open import 2-Dim-Pre.DaggPoSet-Qu.Def-Types.Obj
open import 2-Dim-Pre.DaggPoSet-Qu.Def-Types-pub.Obj

module 2-Dim-Pre.DaggPoSet-Qu.Def-Gens.Objs where

Unit : [Obj]
Unit .Ob = Any.Unit
Unit .Hom _ = PoSet.Unit

Void : [Obj]
Void .Ob = Any.Void
Void .Hom ()

module _ (AB @(A × B) : [2×] [Obj]) where
  Prod2 : [Obj]
  Prod2 .Ob = Any.Prod2 (A .Ob × B .Ob)
  Prod2 .Hom ((a1 × b1) ~ (a2 × b2)) = PoSet.Prod2 (A .Hom (a1 ~ a2) × B .Hom (b1 ~ b2))

module _ (AB @(A + B) : [2×] [Obj]) where
  Summ2 : [Obj]
  Summ2 .Ob = Any.Summ2 (A .Ob × B .Ob)
  Summ2 .Hom (↑₁ a1 ~ ↑₁ a2) = A .Hom (a1 ~ a2)
  Summ2 .Hom (↑₁ a1 ~ ↑₂ b2) = PoSet.Void
  Summ2 .Hom (↑₂ b1 ~ ↑₁ a2) = PoSet.Void
  Summ2 .Hom (↑₂ b1 ~ ↑₂ b2) = B .Hom (b1 ~ b2)
