open import 0-Dim.!quali
open import 1-Dim.Graph.Def-Types.Ob
open import 1-Dim.Graph.Def-Types.Fun
open import 1-Dim.Graph.Def-Types-pub.Ob
open import 1-Dim.Graph.Def-Types-pub.Fun
open import 1-Dim.Graph.Def-Gens.Objs

module 1-Dim.Graph.Def-Gens.Fun where

module _ (A : [Ob]) where
  module Void where
    Init : [Fun] (Void > A)
    Init .f-el = Any.Void.Init _
    Init .f-to ()

  module Unit where
    Term : [Fun] (A > Unit)
    Term .f-el = Any.Unit.Term _
    Term .f-to _ _ = !
--

module Prod2 where
  module _ (AB @(A × B) : [Ob] [×] [Ob]) where
    Prj1 : [Fun] (Prod2 AB > A)
    Prj1 .f-el   = Any.Prod2.Prj1 (A .El   × B .El  )
    Prj1 .f-to _ = Any.Prod2.Prj1 (A .To _ × B .To _)
    Prj2 : [Fun] (Prod2 AB > B)
    Prj2 .f-el   = Any.Prod2.Prj2 (A .El   × B .El  )
    Prj2 .f-to _ = Any.Prod2.Prj2 (A .To _ × B .To _)
  module _ (X : [Ob]) where
    Diag : [Fun] (X > Prod2 (X × X))
    Diag .f-el   = Any.Prod2.Diag (X .El  )
    Diag .f-to _ = Any.Prod2.Diag (X .To _)

module Pow where
  module _ (IA @(I > A) : Any [~] [Ob]) where
    Prj : (i : I) → [Fun] (Pow IA > A)
    Prj i .f-el   = Any.Pow.Prj _ i
    Prj i .f-to _ = Any.ProdI.Prj _ i

    Diag : [Fun] (A > Pow IA)
    Diag .f-el   = Any.Pow.Diag _
    Diag .f-to _ = Any.ProdI.Diag _

module CoPow where
  module _ (IA @(I × A) : Any [×] [Ob]) where
    Inj : (i : I) → [Fun] (A > CoPow IA)
    Inj i .f-el   = Any.CoPow.Inj _ i
    Inj i .f-to _ to = (≡ _) , to

    Glue : [Fun] (CoPow IA > A)
    Glue .f-el   = Any.CoPow.Glue _
    Glue .f-to _ (_ , to) = to

module Summ2 where
  module _ (AB @(A + B) : [Ob] [×] [Ob]) where
    Inj1 : [Fun] (A > Summ2 AB)
    Inj1 .f-el   = Any.Summ2.Inj1 (A .El + B .El)
    Inj1 .f-to _ = ⑴
    Inj2 : [Fun] (B > Summ2 AB)
    Inj2 .f-el   = Any.Summ2.Inj2 (A .El + B .El)
    Inj2 .f-to _ = ⑴
  module _ (X : [Ob]) where
    Glue : [Fun] (Summ2 (X + X) > X)
    Glue .f-el = Any.Summ2.Glue (X .El)
    Glue .f-to (↑₁ _ ~ ↑₁ _) = ⑴
    Glue .f-to (↑₁ _ ~ ↑₂ _) ()
    Glue .f-to (↑₂ _ ~ ↑₁ _) ()
    Glue .f-to (↑₂ _ ~ ↑₂ _) = ⑴

module ProdI where
  module _ (IA @(I ~d A) : Any [~d] λ I → I → [Ob]) where
    Prj : (i : I) → [Fun] (ProdI IA > A i)
    Prj i .f-el   = Any.ProdI.Prj _ i
    Prj i .f-to _ = Any.ProdI.Prj _ i
  module _ (IA @(I ~ A) : Any [~] [Ob]) where
    Diag : [Fun] (A > ProdI (I ~d λ _ → A))
    Diag .f-el   = Any.ProdI.Diag _
    Diag .f-to _ = Any.ProdI.Diag _

module SummI where
  module _ (IA @(I ×d A) : Any [×d] λ I → I → [Ob]) where
    Inj : (i : I) → [Fun] (A i > SummI IA)
    Inj i .f-el   = Any.SummI.Inj _ i
    Inj i .f-to _ = (≡ i) ×d_
  module _ (IA @(I × A) : Any [×] [Ob]) where
    Glue : [Fun] (SummI (I ×d λ _ → A) > A)
    Glue .f-el   = Any.SummI.Glue _
    Glue .f-to _ ((≡ i) ×d to) = to
