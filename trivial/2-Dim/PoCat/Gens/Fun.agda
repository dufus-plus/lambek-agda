open import 0-Dim
import 1-Dim.Graph.Defs as Graph
import 1-Dim.PoSet.Defs as PoSet
import 2-Dim.PoSet-Graph.Defs.Ob as PoSet-Graph
open import 2-Dim.PoCat.Defs.Ob
open import 2-Dim.PoCat.Defs.Fun
open import 2-Dim.PoCat.Defs.Fun-Hom
open import 2-Dim.PoCat.Defs.Fun-Hom-To
open import 2-Dim.PoCat.Oper.Hom|Hom

module 2-Dim.PoCat.Gens.Fun where

open [Ob]
open [oper]
open [prop]
open [Fun]
open Fun-[Hom]
open Fun-Hom-[To]
open PoSet.[Ob]
open PoSet.[is]
open PoSet.[Fun]
open Graph.[Ob]
open Graph.[Fun]
open PoSet-Graph.[Ob]

module _ (2C @(A ~ B) : [2~] [Ob]) where
  module _ (2F @(F ~ G) : [2~] [Fun] 2C) where
    Fun-Hom : PoSet.[Ob]
    Fun-Hom .↓ .Ob = Fun-[Hom] _ (F ~ G)
    Fun-Hom .↓ .To = Fun-Hom-[To] _ _
    Fun-Hom .is .refl tr .↓ a = B .Hom _ .refl (tr .n-ob a)
    Fun-Hom .is .tran (tr1 ~ tr2 ~ tr3) (to12 × to23) .↓ a =
      B .Hom _ .tran _ (to12 .↓ a × to23 .↓ a)

  Fun : [Ob]
  Fun .↓ .Ob = [Fun] (A ~ B)
  Fun .↓ .Hom = Fun-Hom
  Fun .oper .Id F .n-ob a = B .Id (F .F-Ob a)
  Fun .oper .Id F .n-hom-fw _ hom = Hom|Hom-Id B _ (F .F-Hom _ .f-ob hom)
  Fun .oper .Id F .n-hom-bw _ hom = Hom-Id|Hom B _ (F .F-Hom _ .f-ob hom)
  Fun .oper .Mu _ .↓ .f-ob (tr12 × tr23) .n-ob a =
    B .Mu _ .f-ob (tr12 .n-ob a × tr23 .n-ob a)
  Fun .oper .Mu _ .↓ .f-ob (tr12 × tr23) .n-hom-fw _ hom =
    Hom|Hom-Mu B _ _ _ (tr12 .n-hom-fw _ hom × tr23 .n-hom-fw _ hom )
  Fun .oper .Mu _ .↓ .f-ob (tr12 × tr23) .n-hom-bw _ hom =
    Hom-Mu|Hom B _ _ _ (tr12 .n-hom-bw _ hom × tr23 .n-hom-bw _ hom )
  Fun .oper .Mu _ .↓ .f-to _ (to12 × to23) .↓ a =
    B .Mu _ .f-to _ (to12 .↓ a × to23 .↓ a)
  Fun .prop .Assoc-fw _ (tr12 × tr23 × tr34) .↓ a =
    B .Assoc-fw _ (tr12 .n-ob a × tr23 .n-ob a × tr34 .n-ob a)
  Fun .prop .Assoc-bw _ (tr12 × tr23 × tr34) .↓ a =
    B .Assoc-bw _ (tr12 .n-ob a × tr23 .n-ob a × tr34 .n-ob a)
  Fun .prop .LUnit-fw _ tr12 .↓ a = B .LUnit-fw _ (tr12 .n-ob a)
  Fun .prop .LUnit-bw _ tr12 .↓ a = B .LUnit-bw _ (tr12 .n-ob a)
  Fun .prop .RUnit-fw _ tr12 .↓ a = B .RUnit-fw _ (tr12 .n-ob a)
  Fun .prop .RUnit-bw _ tr12 .↓ a = B .RUnit-bw _ (tr12 .n-ob a)
  Fun .prop .BUnit-fw _ .↓ a = B .BUnit-fw _
  Fun .prop .BUnit-bw _ .↓ a = B .BUnit-bw _
