open import 0-Dim.!quali
import 1-Dim.Graph.Def-Gens as Graph
open import 1-Dim.Graph.Def-Types-pub
open import 1-Dim.Set.Def-Types
open import 1-Dim.Set.Def-Types-pub
open import 1-Dim.Set.Def-Opers.Fun
open import 1-Dim.Set.Def-Gens.Objs

module 1-Dim.Set.Def-Gens.Fun where

module _ (A : [Ob]) where
  module Void where
    Init : [Fun] (Void > A)
    Init .↓ = Graph.Void.Init _

  module Unit where
    Term : [Fun] (A > Unit)
    Term .↓ = Graph.Unit.Term _
--

module Prod2 where
  module _ (AB @(A × B) : [Ob] [×] [Ob]) where
    Prj1 : [Fun] (Prod2 (A × B) > A)
    Prj1 .↓ = Graph.Prod2.Prj1 _
    Prj2 : [Fun] (Prod2 (A × B) > B)
    Prj2 .↓ = Graph.Prod2.Prj2 _
  module _ (X : [Ob]) where
    Diag : [Fun] (X > Prod2 (X × X))
    Diag .↓ = Graph.Prod2.Diag _

module Summ2 where
  module _ (AB @(A + B) : [Ob] [×] [Ob]) where
    Inj1 : [Fun] (A > Summ2 (A + B))
    Inj1 .↓ = Graph.Summ2.Inj1 _
    Inj2 : [Fun] (B > Summ2 (A + B))
    Inj2 .↓ = Graph.Summ2.Inj2 _
  module _ (X : [Ob]) where
    Glue : [Fun] (Summ2 (X + X) > X)
    Glue .↓ = Graph.Summ2.Glue _

module _ (AB @(A ~ B) : [2~] [Ob]) where
  ConstF : [Fun] (B > Fun (A > B))
  ConstF .↓ .f-el b .↓ .f-el = Any.Const _ b
  ConstF .↓ .f-el b .↓ .f-to _ _ = B .refl b
  ConstF .↓ .f-to _ bto12 .↓ a = bto12
