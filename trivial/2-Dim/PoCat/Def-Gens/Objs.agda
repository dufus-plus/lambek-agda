open import 0-Dim.!quali
open import 1-Dim.Graph.!publi
open import 1-Dim.PoSet.!publi
open import 2-Dim.PoCat.Def-Types.Ob
open import 2-Dim.PoCat.Def-Types-pub.Ob
import 2-Dim.PoQuiver.Def-Gens.Objs as PoQuiver

module 2-Dim.PoCat.Def-Gens.Objs where

Unit : [Ob]
Unit .It = PoQuiver.Unit
Unit .oper .Id _ = !
Unit .oper .Mu _ = PoSet.Unit.Term _
Unit .prop .Assoc-fw _ _ = !
Unit .prop .Assoc-bw _ _ = !
Unit .prop .LUnit-fw _ _ = !
Unit .prop .LUnit-bw _ _ = !
Unit .prop .RUnit-fw _ _ = !
Unit .prop .RUnit-bw _ _ = !
Unit .prop .BUnit-fw _ = !
Unit .prop .BUnit-bw _ = !

Void : [Ob]
Void .It  = PoQuiver.Void
Void .oper .Id ()
Void .oper .Mu ()
Void .prop .Assoc-fw ()
Void .prop .Assoc-bw ()
Void .prop .LUnit-fw ()
Void .prop .LUnit-bw ()
Void .prop .RUnit-fw ()
Void .prop .RUnit-bw ()
Void .prop .BUnit-fw ()
Void .prop .BUnit-bw ()

module _ (AB @(A × B) : [2×] [Ob]) where
  Prod2 : [Ob]
  Prod2 .It = PoQuiver.Prod2 (A .It × B .It)
  Prod2 .oper .Id _ = A .Id _ × B .Id _
  Prod2 .oper .Mu _ .↓ .f-ob ((ahom12 × bhom12) × (ahom23 × bhom23)) =
    A .Mu _ .f-ob (ahom12 × ahom23) × B .Mu _ .f-ob (bhom12 × bhom23)
  Prod2 .oper .Mu _ .↓ .f-to _ ((ato12 × bto12) × (ato23 × bto23)) =
    A .Mu _ .f-to _ (ato12 × ato23) × B .Mu _ .f-to _ (bto12 × bto23)
  Prod2 .prop .Assoc-fw _ ((ahom12 × bhom12) × (ahom23 × bhom23) × (ahom34 × bhom34)) =
    A .Assoc-fw _ (ahom12 × ahom23 × ahom34) × B .Assoc-fw _ (bhom12 × bhom23 × bhom34)
  Prod2 .prop .Assoc-bw _ ((ahom12 × bhom12) × (ahom23 × bhom23) × (ahom34 × bhom34)) =
    A .Assoc-bw _ (ahom12 × ahom23 × ahom34) × B .Assoc-bw _ (bhom12 × bhom23 × bhom34)
  Prod2 .prop .LUnit-fw _ (ahom12 × bhom12) =
    A .LUnit-fw _ ahom12 × B .LUnit-fw _ bhom12
  Prod2 .prop .LUnit-bw _ (ahom12 × bhom12) =
    A .LUnit-bw _ ahom12 × B .LUnit-bw _ bhom12
  Prod2 .prop .RUnit-fw _ (ahom12 × bhom12) =
    A .RUnit-fw _ ahom12 × B .RUnit-fw _ bhom12
  Prod2 .prop .RUnit-bw _ (ahom12 × bhom12) =
    A .RUnit-bw _ ahom12 × B .RUnit-bw _ bhom12
  Prod2 .prop .BUnit-fw _ = A .BUnit-fw _ × B .BUnit-fw _
  Prod2 .prop .BUnit-bw _ = A .BUnit-bw _ × B .BUnit-bw _

module _ (AB @(A + B) : [Ob] [×] [Ob]) where
  Summ2 : [Ob]
  Summ2 .It = PoQuiver.Summ2 (A .It + B .It)
  Summ2 .oper .Id (↑₁ _) = A .Id _
  Summ2 .oper .Id (↑₂ _) = B .Id _

  Summ2 .oper .Mu (↑₁ _ ~ ↑₁ _ ~ ↑₁ _) .↓ .f-ob ahom123 = A .Mu _ .f-ob ahom123
  Summ2 .oper .Mu (↑₁ _ ~ ↑₁ _ ~ ↑₂ _) .↓ .f-ob ()
  Summ2 .oper .Mu (↑₁ _ ~ ↑₂ _ ~ ↑₁ _) .↓ .f-ob ()
  Summ2 .oper .Mu (↑₁ _ ~ ↑₂ _ ~ ↑₂ _) .↓ .f-ob ()
  Summ2 .oper .Mu (↑₂ _ ~ ↑₁ _ ~ ↑₁ _) .↓ .f-ob ()
  Summ2 .oper .Mu (↑₂ _ ~ ↑₁ _ ~ ↑₂ _) .↓ .f-ob ()
  Summ2 .oper .Mu (↑₂ _ ~ ↑₂ _ ~ ↑₁ _) .↓ .f-ob ()
  Summ2 .oper .Mu (↑₂ _ ~ ↑₂ _ ~ ↑₂ _) .↓ .f-ob bhom123 = B .Mu _ .f-ob bhom123

  Summ2 .oper .Mu (↑₁ _ ~ ↑₁ _ ~ ↑₁ _) .↓ .f-to _ ato123 = A .Mu _ .f-to _ ato123
  Summ2 .oper .Mu (↑₁ _ ~ ↑₁ _ ~ ↑₂ _) .↓ .f-to ()
  Summ2 .oper .Mu (↑₁ _ ~ ↑₂ _ ~ ↑₁ _) .↓ .f-to ()
  Summ2 .oper .Mu (↑₁ _ ~ ↑₂ _ ~ ↑₂ _) .↓ .f-to ()
  Summ2 .oper .Mu (↑₂ _ ~ ↑₁ _ ~ ↑₁ _) .↓ .f-to ()
  Summ2 .oper .Mu (↑₂ _ ~ ↑₁ _ ~ ↑₂ _) .↓ .f-to ()
  Summ2 .oper .Mu (↑₂ _ ~ ↑₂ _ ~ ↑₁ _) .↓ .f-to ()
  Summ2 .oper .Mu (↑₂ _ ~ ↑₂ _ ~ ↑₂ _) .↓ .f-to _ bto123 = B .Mu _ .f-to _ bto123

  Summ2 .prop .Assoc-fw (↑₁ _ ~ ↑₁ _ ~ ↑₁ _ ~ ↑₁ _) 3hom = A .Assoc-fw _ 3hom
  Summ2 .prop .Assoc-fw (↑₁ _ ~ ↑₁ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .prop .Assoc-fw (↑₁ _ ~ ↑₁ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .prop .Assoc-fw (↑₁ _ ~ ↑₁ _ ~ ↑₂ _ ~ ↑₂ _) ()
  Summ2 .prop .Assoc-fw (↑₁ _ ~ ↑₂ _ ~ ↑₁ _ ~ ↑₁ _) ()
  Summ2 .prop .Assoc-fw (↑₁ _ ~ ↑₂ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .prop .Assoc-fw (↑₁ _ ~ ↑₂ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .prop .Assoc-fw (↑₁ _ ~ ↑₂ _ ~ ↑₂ _ ~ ↑₂ _) ()
  Summ2 .prop .Assoc-fw (↑₂ _ ~ ↑₁ _ ~ ↑₁ _ ~ ↑₁ _) ()
  Summ2 .prop .Assoc-fw (↑₂ _ ~ ↑₁ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .prop .Assoc-fw (↑₂ _ ~ ↑₁ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .prop .Assoc-fw (↑₂ _ ~ ↑₁ _ ~ ↑₂ _ ~ ↑₂ _) ()
  Summ2 .prop .Assoc-fw (↑₂ _ ~ ↑₂ _ ~ ↑₁ _ ~ ↑₁ _) ()
  Summ2 .prop .Assoc-fw (↑₂ _ ~ ↑₂ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .prop .Assoc-fw (↑₂ _ ~ ↑₂ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .prop .Assoc-fw (↑₂ _ ~ ↑₂ _ ~ ↑₂ _ ~ ↑₂ _) 3hom = B .Assoc-fw _ 3hom

  Summ2 .prop .Assoc-bw (↑₁ _ ~ ↑₁ _ ~ ↑₁ _ ~ ↑₁ _) 3hom = A .Assoc-bw _ 3hom
  Summ2 .prop .Assoc-bw (↑₁ _ ~ ↑₁ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .prop .Assoc-bw (↑₁ _ ~ ↑₁ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .prop .Assoc-bw (↑₁ _ ~ ↑₁ _ ~ ↑₂ _ ~ ↑₂ _) ()
  Summ2 .prop .Assoc-bw (↑₁ _ ~ ↑₂ _ ~ ↑₁ _ ~ ↑₁ _) ()
  Summ2 .prop .Assoc-bw (↑₁ _ ~ ↑₂ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .prop .Assoc-bw (↑₁ _ ~ ↑₂ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .prop .Assoc-bw (↑₁ _ ~ ↑₂ _ ~ ↑₂ _ ~ ↑₂ _) ()
  Summ2 .prop .Assoc-bw (↑₂ _ ~ ↑₁ _ ~ ↑₁ _ ~ ↑₁ _) ()
  Summ2 .prop .Assoc-bw (↑₂ _ ~ ↑₁ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .prop .Assoc-bw (↑₂ _ ~ ↑₁ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .prop .Assoc-bw (↑₂ _ ~ ↑₁ _ ~ ↑₂ _ ~ ↑₂ _) ()
  Summ2 .prop .Assoc-bw (↑₂ _ ~ ↑₂ _ ~ ↑₁ _ ~ ↑₁ _) ()
  Summ2 .prop .Assoc-bw (↑₂ _ ~ ↑₂ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .prop .Assoc-bw (↑₂ _ ~ ↑₂ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .prop .Assoc-bw (↑₂ _ ~ ↑₂ _ ~ ↑₂ _ ~ ↑₂ _) 3hom = B .Assoc-bw _ 3hom

  Summ2 .prop .LUnit-fw (↑₁ _ ~ ↑₁ _) hom12 = A .LUnit-fw _ hom12
  Summ2 .prop .LUnit-fw (↑₁ _ ~ ↑₂ _) ()
  Summ2 .prop .LUnit-fw (↑₂ _ ~ ↑₁ _) ()
  Summ2 .prop .LUnit-fw (↑₂ _ ~ ↑₂ _) hom12 = B .LUnit-fw _ hom12
  Summ2 .prop .LUnit-bw (↑₁ _ ~ ↑₁ _) hom12 = A .LUnit-bw _ hom12
  Summ2 .prop .LUnit-bw (↑₁ _ ~ ↑₂ _) ()
  Summ2 .prop .LUnit-bw (↑₂ _ ~ ↑₁ _) ()
  Summ2 .prop .LUnit-bw (↑₂ _ ~ ↑₂ _) hom12 = B .LUnit-bw _ hom12
  Summ2 .prop .RUnit-fw (↑₁ _ ~ ↑₁ _) hom12 = A .RUnit-fw _ hom12
  Summ2 .prop .RUnit-fw (↑₁ _ ~ ↑₂ _) ()
  Summ2 .prop .RUnit-fw (↑₂ _ ~ ↑₁ _) ()
  Summ2 .prop .RUnit-fw (↑₂ _ ~ ↑₂ _) hom12 = B .RUnit-fw _ hom12
  Summ2 .prop .RUnit-bw (↑₁ _ ~ ↑₁ _) hom12 = A .RUnit-bw _ hom12
  Summ2 .prop .RUnit-bw (↑₁ _ ~ ↑₂ _) ()
  Summ2 .prop .RUnit-bw (↑₂ _ ~ ↑₁ _) ()
  Summ2 .prop .RUnit-bw (↑₂ _ ~ ↑₂ _) hom12 = B .RUnit-bw _ hom12

  Summ2 .prop .BUnit-fw (↑₁ _) = A .BUnit-fw _
  Summ2 .prop .BUnit-fw (↑₂ _) = B .BUnit-fw _
  Summ2 .prop .BUnit-bw (↑₁ _) = A .BUnit-bw _
  Summ2 .prop .BUnit-bw (↑₂ _) = B .BUnit-bw _
