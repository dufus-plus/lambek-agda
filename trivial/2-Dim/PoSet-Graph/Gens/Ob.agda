open import 0-Dim
import 1-Dim.PoSet.Gens.Ob as PoSet
open import 2-Dim.PoSet-Graph.Defs.Ob

module 2-Dim.PoSet-Graph.Gens.Ob where

open [Ob]

Unit : [Ob]
Unit .Ob = Any.Unit
Unit .Hom _ = PoSet.Unit

Void : [Ob]
Void .Ob = Any.Void
Void .Hom (() ~ ())

module _ (AB @(A × B) : [Ob] [×] [Ob]) where
  Prod : [Ob]
  Prod .Ob = Any.Prod (A .Ob × B .Ob)
  Prod .Hom ((a1 × b1) ~ (a2 × b2)) = PoSet.Prod (A .Hom (a1 ~ a2) × B .Hom (b1 ~ b2))

module _ (AB @(A + B) : [Ob] [×] [Ob]) where
  Summ : [Ob]
  Summ .Ob = Any.Summ (A .Ob × B .Ob)
  Summ .Hom (↑₁ a1 ~ ↑₁ a2) = A .Hom (a1 ~ a2)
  Summ .Hom (↑₁ a1 ~ ↑₂ b2) = PoSet.Void
  Summ .Hom (↑₂ b1 ~ ↑₁ a2) = PoSet.Void
  Summ .Hom (↑₂ b1 ~ ↑₂ b2) = B .Hom (b1 ~ b2)
