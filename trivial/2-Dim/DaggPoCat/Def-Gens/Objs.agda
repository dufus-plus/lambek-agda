open import 0-Dim.!quali
open import 1-Dim.Graph.!publi
import 1-Dim.PoSet.Def-Gens as PoSet
open import 1-Dim.PoSet.Def-Types-pub
open import 2-Dim.DaggPoCat.Def-Types.Obj
open import 2-Dim.DaggPoCat.Def-Types-pub.Obj
import 2-Dim-Pre.PoSet-Qu.Def-Types.Obj as PoSet-Qu
open import 2-Dim-Pre.PoSet-Qu.Def-Types-pub.Obj
import 2-Dim-Pre.PoSet-Qu.Def-Gens.Objs as PoSet-Qu

module 2-Dim.DaggPoCat.Def-Gens.Objs where

Unit : [Obj]
Unit     .Ob  = PoSet-Qu.Unit .Ob
Unit .is .Hom = PoSet-Qu.Unit .Hom
Unit .is .oper .Id _   = !
Unit .is .oper .Mu _   = PoSet.Unit.Term _
Unit .is .oper .Dagg _ = PoSet.Unit.Term _
Unit .is .prop .assoc-fw _ _ = !
Unit .is .prop .assoc-bw _ _ = !
Unit .is .prop .lunit-fw _ _ = !
Unit .is .prop .lunit-bw _ _ = !
Unit .is .prop .runit-fw _ _ = !
Unit .is .prop .runit-bw _ _ = !
Unit .is .prop .bunit-fw _ = !
Unit .is .prop .bunit-bw _ = !
Unit .is .prop .id-dagg-fw _ = !
Unit .is .prop .id-dagg-bw _ = !
Unit .is .prop .mu-dagg-fw _ _ = !
Unit .is .prop .mu-dagg-bw _ _ = !

Void : [Obj]
Void     .Ob  = PoSet-Qu.Void .Ob
Void .is .Hom = PoSet-Qu.Void .Hom
Void .is .oper .Id ()
Void .is .oper .Mu ()
Void .is .oper .Dagg ()
Void .is .prop .assoc-fw ()
Void .is .prop .assoc-bw ()
Void .is .prop .lunit-fw ()
Void .is .prop .lunit-bw ()
Void .is .prop .runit-fw ()
Void .is .prop .runit-bw ()
Void .is .prop .bunit-fw ()
Void .is .prop .bunit-bw ()

module _ (AB @(A × B) : [2×] [Obj]) where
  Prod2 : [Obj]
  Prod2     .Ob  = PoSet-Qu.Prod2 (Qu A × Qu B) .Ob
  Prod2 .is .Hom = PoSet-Qu.Prod2 (Qu A × Qu B) .Hom
  Prod2 .is .oper .Id _ = A .Id _ × B .Id _
  Prod2 .is .oper .Mu _ .↓ .f-el ((ahom12 × bhom12) × (ahom23 × bhom23)) =
    A .Mu _ .f-el (ahom12 × ahom23) × B .Mu _ .f-el (bhom12 × bhom23)
  Prod2 .is .oper .Mu _ .↓ .f-to _ ((ato12 × bto12) × (ato23 × bto23)) =
    A .Mu _ .f-to _ (ato12 × ato23) × B .Mu _ .f-to _ (bto12 × bto23)
  Prod2 .is .oper .Dagg _ .↓ .f-el (ahom12 × bhom12) =
    A .Dagg _ .f-el ahom12 × B .Dagg _ .f-el bhom12
  Prod2 .is .oper .Dagg _ .↓ .f-to _ (ato12 × bto12) =
    A .Dagg _ .f-to _ ato12 × B .Dagg _ .f-to _ bto12
  Prod2 .is .prop .assoc-fw _ ((ahom12 × bhom12) × (ahom23 × bhom23) × (ahom34 × bhom34)) =
    A .assoc-fw _ (ahom12 × ahom23 × ahom34) × B .assoc-fw _ (bhom12 × bhom23 × bhom34)
  Prod2 .is .prop .assoc-bw _ ((ahom12 × bhom12) × (ahom23 × bhom23) × (ahom34 × bhom34)) =
    A .assoc-bw _ (ahom12 × ahom23 × ahom34) × B .assoc-bw _ (bhom12 × bhom23 × bhom34)
  Prod2 .is .prop .lunit-fw _ (ahom12 × bhom12) = A .lunit-fw _ ahom12 × B .lunit-fw _ bhom12
  Prod2 .is .prop .lunit-bw _ (ahom12 × bhom12) = A .lunit-bw _ ahom12 × B .lunit-bw _ bhom12
  Prod2 .is .prop .runit-fw _ (ahom12 × bhom12) = A .runit-fw _ ahom12 × B .runit-fw _ bhom12
  Prod2 .is .prop .runit-bw _ (ahom12 × bhom12) = A .runit-bw _ ahom12 × B .runit-bw _ bhom12
  Prod2 .is .prop .bunit-fw _ = A .bunit-fw _ × B .bunit-fw _
  Prod2 .is .prop .bunit-bw _ = A .bunit-bw _ × B .bunit-bw _
  Prod2 .is .prop .id-dagg-fw _ = A .id-dagg-fw _ × B .id-dagg-fw _
  Prod2 .is .prop .id-dagg-bw _ = A .id-dagg-bw _ × B .id-dagg-bw _
  Prod2 .is .prop .mu-dagg-fw _ ((ahom12 × bhom12) × (ahom23 × bhom23)) =
    A .mu-dagg-fw _ (ahom12 × ahom23) × B .mu-dagg-fw _ (bhom12 × bhom23)
  Prod2 .is .prop .mu-dagg-bw _ ((ahom12 × bhom12) × (ahom23 × bhom23)) =
    A .mu-dagg-bw _ (ahom12 × ahom23) × B .mu-dagg-bw _ (bhom12 × bhom23)

module _ (AB @(A + B) : [2×] [Obj]) where
  Summ2 : [Obj]
  Summ2     .Ob  = PoSet-Qu.Summ2 (Qu A + Qu B) .Ob
  Summ2 .is .Hom = PoSet-Qu.Summ2 (Qu A + Qu B) .Hom
  Summ2 .is .oper .Id (↑₁ _) = A .Id _
  Summ2 .is .oper .Id (↑₂ _) = B .Id _

  Summ2 .is .oper .Mu (↑₁ _ ~ ↑₁ _ ~ ↑₁ _) .↓ .f-el ahom123 = A .Mu _ .f-el ahom123
  Summ2 .is .oper .Mu (↑₁ _ ~ ↑₁ _ ~ ↑₂ _) .↓ .f-el ()
  Summ2 .is .oper .Mu (↑₁ _ ~ ↑₂ _ ~ ↑₁ _) .↓ .f-el ()
  Summ2 .is .oper .Mu (↑₁ _ ~ ↑₂ _ ~ ↑₂ _) .↓ .f-el ()
  Summ2 .is .oper .Mu (↑₂ _ ~ ↑₁ _ ~ ↑₁ _) .↓ .f-el ()
  Summ2 .is .oper .Mu (↑₂ _ ~ ↑₁ _ ~ ↑₂ _) .↓ .f-el ()
  Summ2 .is .oper .Mu (↑₂ _ ~ ↑₂ _ ~ ↑₁ _) .↓ .f-el ()
  Summ2 .is .oper .Mu (↑₂ _ ~ ↑₂ _ ~ ↑₂ _) .↓ .f-el bhom123 = B .Mu _ .f-el bhom123

  Summ2 .is .oper .Mu (↑₁ _ ~ ↑₁ _ ~ ↑₁ _) .↓ .f-to _ ato123 = A .Mu _ .f-to _ ato123
  Summ2 .is .oper .Mu (↑₁ _ ~ ↑₁ _ ~ ↑₂ _) .↓ .f-to ()
  Summ2 .is .oper .Mu (↑₁ _ ~ ↑₂ _ ~ ↑₁ _) .↓ .f-to ()
  Summ2 .is .oper .Mu (↑₁ _ ~ ↑₂ _ ~ ↑₂ _) .↓ .f-to ()
  Summ2 .is .oper .Mu (↑₂ _ ~ ↑₁ _ ~ ↑₁ _) .↓ .f-to ()
  Summ2 .is .oper .Mu (↑₂ _ ~ ↑₁ _ ~ ↑₂ _) .↓ .f-to ()
  Summ2 .is .oper .Mu (↑₂ _ ~ ↑₂ _ ~ ↑₁ _) .↓ .f-to ()
  Summ2 .is .oper .Mu (↑₂ _ ~ ↑₂ _ ~ ↑₂ _) .↓ .f-to _ bto123 = B .Mu _ .f-to _ bto123

  Summ2 .is .oper .Dagg (↑₁ _ ~ ↑₁ _) .↓ .f-el ahom12 = A .Dagg _ .f-el ahom12
  Summ2 .is .oper .Dagg (↑₁ _ ~ ↑₂ _) .↓ .f-el ()
  Summ2 .is .oper .Dagg (↑₂ _ ~ ↑₁ _) .↓ .f-el ()
  Summ2 .is .oper .Dagg (↑₂ _ ~ ↑₂ _) .↓ .f-el bhom12 = B .Dagg _ .f-el bhom12

  Summ2 .is .oper .Dagg (↑₁ _ ~ ↑₁ _) .↓ .f-to _ ato12 = A .Dagg _ .f-to _ ato12
  Summ2 .is .oper .Dagg (↑₁ _ ~ ↑₂ _) .↓ .f-to ()
  Summ2 .is .oper .Dagg (↑₂ _ ~ ↑₁ _) .↓ .f-to ()
  Summ2 .is .oper .Dagg (↑₂ _ ~ ↑₂ _) .↓ .f-to _ bto12 = B .Dagg _ .f-to _ bto12

  Summ2 .is .prop .assoc-fw (↑₁ _ ~ ↑₁ _ ~ ↑₁ _ ~ ↑₁ _) 3hom = A .assoc-fw _ 3hom
  Summ2 .is .prop .assoc-fw (↑₁ _ ~ ↑₁ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .prop .assoc-fw (↑₁ _ ~ ↑₁ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .prop .assoc-fw (↑₁ _ ~ ↑₁ _ ~ ↑₂ _ ~ ↑₂ _) ()
  Summ2 .is .prop .assoc-fw (↑₁ _ ~ ↑₂ _ ~ ↑₁ _ ~ ↑₁ _) ()
  Summ2 .is .prop .assoc-fw (↑₁ _ ~ ↑₂ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .prop .assoc-fw (↑₁ _ ~ ↑₂ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .prop .assoc-fw (↑₁ _ ~ ↑₂ _ ~ ↑₂ _ ~ ↑₂ _) ()
  Summ2 .is .prop .assoc-fw (↑₂ _ ~ ↑₁ _ ~ ↑₁ _ ~ ↑₁ _) ()
  Summ2 .is .prop .assoc-fw (↑₂ _ ~ ↑₁ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .prop .assoc-fw (↑₂ _ ~ ↑₁ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .prop .assoc-fw (↑₂ _ ~ ↑₁ _ ~ ↑₂ _ ~ ↑₂ _) ()
  Summ2 .is .prop .assoc-fw (↑₂ _ ~ ↑₂ _ ~ ↑₁ _ ~ ↑₁ _) ()
  Summ2 .is .prop .assoc-fw (↑₂ _ ~ ↑₂ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .prop .assoc-fw (↑₂ _ ~ ↑₂ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .prop .assoc-fw (↑₂ _ ~ ↑₂ _ ~ ↑₂ _ ~ ↑₂ _) 3hom = B .assoc-fw _ 3hom

  Summ2 .is .prop .assoc-bw (↑₁ _ ~ ↑₁ _ ~ ↑₁ _ ~ ↑₁ _) 3hom = A .assoc-bw _ 3hom
  Summ2 .is .prop .assoc-bw (↑₁ _ ~ ↑₁ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .prop .assoc-bw (↑₁ _ ~ ↑₁ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .prop .assoc-bw (↑₁ _ ~ ↑₁ _ ~ ↑₂ _ ~ ↑₂ _) ()
  Summ2 .is .prop .assoc-bw (↑₁ _ ~ ↑₂ _ ~ ↑₁ _ ~ ↑₁ _) ()
  Summ2 .is .prop .assoc-bw (↑₁ _ ~ ↑₂ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .prop .assoc-bw (↑₁ _ ~ ↑₂ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .prop .assoc-bw (↑₁ _ ~ ↑₂ _ ~ ↑₂ _ ~ ↑₂ _) ()
  Summ2 .is .prop .assoc-bw (↑₂ _ ~ ↑₁ _ ~ ↑₁ _ ~ ↑₁ _) ()
  Summ2 .is .prop .assoc-bw (↑₂ _ ~ ↑₁ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .prop .assoc-bw (↑₂ _ ~ ↑₁ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .prop .assoc-bw (↑₂ _ ~ ↑₁ _ ~ ↑₂ _ ~ ↑₂ _) ()
  Summ2 .is .prop .assoc-bw (↑₂ _ ~ ↑₂ _ ~ ↑₁ _ ~ ↑₁ _) ()
  Summ2 .is .prop .assoc-bw (↑₂ _ ~ ↑₂ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .prop .assoc-bw (↑₂ _ ~ ↑₂ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .prop .assoc-bw (↑₂ _ ~ ↑₂ _ ~ ↑₂ _ ~ ↑₂ _) 3hom = B .assoc-bw _ 3hom

  Summ2 .is .prop .lunit-fw (↑₁ _ ~ ↑₁ _) hom12 = A .lunit-fw _ hom12
  Summ2 .is .prop .lunit-fw (↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .prop .lunit-fw (↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .prop .lunit-fw (↑₂ _ ~ ↑₂ _) hom12 = B .lunit-fw _ hom12
  Summ2 .is .prop .lunit-bw (↑₁ _ ~ ↑₁ _) hom12 = A .lunit-bw _ hom12
  Summ2 .is .prop .lunit-bw (↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .prop .lunit-bw (↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .prop .lunit-bw (↑₂ _ ~ ↑₂ _) hom12 = B .lunit-bw _ hom12
  Summ2 .is .prop .runit-fw (↑₁ _ ~ ↑₁ _) hom12 = A .runit-fw _ hom12
  Summ2 .is .prop .runit-fw (↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .prop .runit-fw (↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .prop .runit-fw (↑₂ _ ~ ↑₂ _) hom12 = B .runit-fw _ hom12
  Summ2 .is .prop .runit-bw (↑₁ _ ~ ↑₁ _) hom12 = A .runit-bw _ hom12
  Summ2 .is .prop .runit-bw (↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .prop .runit-bw (↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .prop .runit-bw (↑₂ _ ~ ↑₂ _) hom12 = B .runit-bw _ hom12

  Summ2 .is .prop .bunit-fw (↑₁ _) = A .bunit-fw _
  Summ2 .is .prop .bunit-fw (↑₂ _) = B .bunit-fw _
  Summ2 .is .prop .bunit-bw (↑₁ _) = A .bunit-bw _
  Summ2 .is .prop .bunit-bw (↑₂ _) = B .bunit-bw _

  Summ2 .is .prop .id-dagg-fw (↑₁ _) = A .id-dagg-fw _
  Summ2 .is .prop .id-dagg-fw (↑₂ _) = B .id-dagg-fw _
  Summ2 .is .prop .id-dagg-bw (↑₁ _) = A .id-dagg-bw _
  Summ2 .is .prop .id-dagg-bw (↑₂ _) = B .id-dagg-bw _

  Summ2 .is .prop .mu-dagg-fw (↑₁ _ ~ ↑₁ _ ~ ↑₁ _) ahom123 = A .mu-dagg-fw _ ahom123
  Summ2 .is .prop .mu-dagg-fw (↑₁ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .prop .mu-dagg-fw (↑₁ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .prop .mu-dagg-fw (↑₁ _ ~ ↑₂ _ ~ ↑₂ _) ()
  Summ2 .is .prop .mu-dagg-fw (↑₂ _ ~ ↑₁ _ ~ ↑₁ _) ()
  Summ2 .is .prop .mu-dagg-fw (↑₂ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .prop .mu-dagg-fw (↑₂ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .prop .mu-dagg-fw (↑₂ _ ~ ↑₂ _ ~ ↑₂ _) bhom123 = B .mu-dagg-fw _ bhom123

  Summ2 .is .prop .mu-dagg-bw (↑₁ _ ~ ↑₁ _ ~ ↑₁ _) ahom123 = A .mu-dagg-bw _ ahom123
  Summ2 .is .prop .mu-dagg-bw (↑₁ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .prop .mu-dagg-bw (↑₁ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .prop .mu-dagg-bw (↑₁ _ ~ ↑₂ _ ~ ↑₂ _) ()
  Summ2 .is .prop .mu-dagg-bw (↑₂ _ ~ ↑₁ _ ~ ↑₁ _) ()
  Summ2 .is .prop .mu-dagg-bw (↑₂ _ ~ ↑₁ _ ~ ↑₂ _) ()
  Summ2 .is .prop .mu-dagg-bw (↑₂ _ ~ ↑₂ _ ~ ↑₁ _) ()
  Summ2 .is .prop .mu-dagg-bw (↑₂ _ ~ ↑₂ _ ~ ↑₂ _) bhom123 = B .mu-dagg-bw _ bhom123
