open import 0-Dim
open import 1-Dim.Set.Defs
open import 1-Dim.Set.Gens.Ob
open import 1-Dim.Set.Gens.Exp-Ob
open import 1-Dim.Set.Gens.Hom

module 1-Dim.Set.Extr.Unit where

module Unit where

  Δ : Cat.[Fun] (Cat.Set > Cat.Unit)
  Δ = Cat.Term Cat.Set

  F : Cat.[Fun] (Cat.Unit > Cat.Set)
  F .$f-el _ = Unit

  HardAdj : Cat.[HardAdj] (Δ ~ UnitF)
  HardAdj = _

UnitF = Unit.F
