open import 0-Dim
open import 1-Dim.Set.Defs
open import 1-Dim.Set.Gens.Ob
open import 1-Dim.Set.Gens.Exp-Ob
open import 1-Dim.Set.Gens.Hom

module 1-Dim.Set.Extra.Prod where

module Prod where

  Δ : Cat.[Fun] (Cat.Set > Cat.Prod (Cat.Set × Cat.Set))
  Δ = Cat.Diag Cat.Set 

  F : Cat.[Fun] (Cat.Prod-FOb (Cat.Set × Cat.Set) > Cat.Set)
  F .$F-Ob = Prod

  Adj : Cat.Adj (Δ ~ ProdF)
  Adj = _

ProdF = Prod.F