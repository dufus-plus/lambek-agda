open import 0-Dim.!quali
open import 1-Dim.Graph.!publi
open import 1-Dim.PoSet.!publi
import 2-Dim.PoQuiver.Def-Types.Ob as PoQuiver
open import 2-Dim.PoQuiver.Def-Types-pub.Ob
open import 2-Dim.PoCat.Def-Types
open import 2-Dim.PoCat.Def-Types-pub
open import 2-Dim.PoCat.Def-Opers.Hom|Hom

module 2-Dim.PoCat.Def-Gens.Fun where

module _ (2C @(A ~ B) : [2~] [Ob]) where
  module _ (2F @(F ~ G) : [2~] [Fun] 2C) where
    Fun-Hom : PoSet.[Ob]
    Fun-Hom .It .Ob = Fun-[Hom] _ (F ~ G)
    Fun-Hom .It .To = Fun-Hom-[To] _ _
    Fun-Hom .is .refl tr .↓ a = B .Hom _ .refl (tr .n-ob a)
    Fun-Hom .is .tran (tr1 ~ tr2 ~ tr3) (to12 × to23) .↓ a =
      B .Hom _ .tran _ (to12 .↓ a × to23 .↓ a)

  Fun : [Ob]
  Fun .It .Ob = [Fun] (A ~ B)
  Fun .It .Hom = Fun-Hom
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
