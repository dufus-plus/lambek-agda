open import 0-Dim
open import 1-Dim.Graph
open import 1-Dim.Set.Defs
open import 1-Dim.Set.Gens.Ob
open import 1-Dim.Set.Gens.Exp

module 1-Dim.Set.Gens.Fun where

open [Ob]
open [Fun]
open Fun-[To]
open Graph.[Fun]

module _ (A : [Ob]) where
  module Void where
    Init-nOb : [Fun] (Void > A)
    Init-nOb .↓ = Graph.Void.Init-nOb (A .↓)

  module Unit where
    Term-nOb : [Fun] (A > Unit)
    Term-nOb .↓ = Graph.Unit.Term-nOb (A .↓)
--

module Prod where
  module _ ((A × B) : [Ob] [×] [Ob]) where
    Prj1-nOb : [Fun] (Prod (A × B) > A)
    Prj1-nOb .↓ = Graph.Prod.Prj1-nOb (A .↓ × B .↓)
    Prj2-nOb : [Fun] (Prod (A × B) > B)
    Prj2-nOb .↓ = Graph.Prod.Prj2-nOb (A .↓ × B .↓)
  module _ (X : [Ob]) where
    Diag-nOb : [Fun] (X > Prod (X × X))
    Diag-nOb .↓ = Graph.Prod.Diag-nOb (X .↓)
module Summ where
  module _ ((A + B) : [Ob] [×] [Ob]) where
    Inj1-nOb : [Fun] (A > Summ (A + B))
    Inj1-nOb .↓ = Graph.Summ.Inj1-nOb (A .↓ + B .↓)
    Inj2-nOb : [Fun] (B > Summ (A + B))
    Inj2-nOb .↓ = Graph.Summ.Inj2-nOb (A .↓ + B .↓)
  module _ (X : [Ob]) where
    Glue-nOb : [Fun] (Summ (X + X) > X)
    Glue-nOb .↓ = Graph.Summ.Glue-nOb (X .↓)

module _ (AB @(A ~ B) : [2~] [Ob]) where
  ConstF : [Fun] (B > Fun (A > B))
  ConstF .↓ .f-ob b .↓ .f-ob = Any.Const _ b
  ConstF .↓ .f-ob b .↓ .f-to _ _ = B .refl b
  ConstF .↓ .f-to _ bto12 .↓ a = bto12
