open import 0-Dim.!quali
import 1-Dim.PoSet.Def-Gens as PoSet
open import 1-Dim.PoSet.Def-Types-pub
open import 2-Dim-Pre.DaggPoSet-Qu.Def-Types.Obj
open import 2-Dim-Pre.DaggPoSet-Qu.Def-Types-pub.Obj

module 2-Dim-Pre.DaggPoSet-Qu.Def-Gens.Objs where

Unit : [Obj]
Unit .Ob = Any.Unit
Unit .Hom _ = PoSet.Unit
Unit .Dagg _ = PoSet.Unit.Term _

Void : [Obj]
Void .Ob = Any.Void
Void .Hom ()
Void .Dagg ()

module _ (AB @(A × B) : [2×] [Obj]) where
  Prod2 : [Obj]
  Prod2 .Ob = Any.Prod2 (A .Ob × B .Ob)
  Prod2 .Hom ((a1 × b1) ~ (a2 × b2)) = PoSet.Prod2 (A .Hom (a1 ~ a2) × B .Hom (b1 ~ b2))
  Prod2 .Dagg _ = PoSet.Prod2.Prod2-Fun _ .f-el (A .Dagg _ × B .Dagg _)

module _ (AB @(A + B) : [2×] [Obj]) where
  Summ2 : [Obj]
  Summ2 .Ob = Any.Summ2 (A .Ob × B .Ob)
  Summ2 .Hom  (↑₁ a1 ~ ↑₁ a2) = A .Hom (a1 ~ a2)
  Summ2 .Hom  (↑₁ a1 ~ ↑₂ b2) = PoSet.Void
  Summ2 .Hom  (↑₂ b1 ~ ↑₁ a2) = PoSet.Void
  Summ2 .Hom  (↑₂ b1 ~ ↑₂ b2) = B .Hom (b1 ~ b2)
  Summ2 .Dagg (↑₁ a1 ~ ↑₁ a2) = A .Dagg (a1 ~ a2)
  Summ2 .Dagg (↑₁ a1 ~ ↑₂ b2) = PoSet.Void.Init _
  Summ2 .Dagg (↑₂ b1 ~ ↑₁ a2) = PoSet.Void.Init _
  Summ2 .Dagg (↑₂ b1 ~ ↑₂ b2) = B .Dagg (b1 ~ b2)
