open import 0-Dim.!quali
open import 1-Dim.Graph.!publi
open import 1-Dim.PoSet.!publi
import 2-Dim-Pre.PoSet-Qu.Def-Types.Obj as PoSet-Qu
open import 2-Dim-Pre.PoSet-Qu.Def-Types-pub.Obj
open import 2-Dim.PoCat.Def-Types
open import 2-Dim.PoCat.Def-Types-pub
open import 2-Dim.PoCat.Def-Opers.Hom|Hom

module 2-Dim.PoCat.Def-Gens.Fun where

module _ (2C @(A ~ B) : [2~] [Obj]) where
  module _ (2F @(F ~ G) : [2~] [Fun] 2C) where
    Fun-Hom : PoSet.[Ob]
    Fun-Hom .It .El = Fun-[Hom] _ (F ~ G)
    Fun-Hom .It .To = Fun-Hom-[To] _ _
    Fun-Hom .is .refl tr .↓ a = B .Hom _ .refl (tr .n-ob a)
    Fun-Hom .is .tran (tr1 ~ tr2 ~ tr3) (to12 × to23) .↓ a =
      B .Hom _ .tran _ (to12 .↓ a × to23 .↓ a)

  Fun : [Obj]
  Fun     .Ob  = [Fun] (A ~ B)
  Fun .is .Hom = Fun-Hom
  Fun .is .oper .Id F .n-ob a = B .Id (F .f-ob a)
  Fun .is .oper .Id F .n-hom-fw _ hom = Hom|Hom-Id B _ (F .f-hom-el _ hom)
  Fun .is .oper .Id F .n-hom-bw _ hom = Hom-Id|Hom B _ (F .f-hom-el _ hom)
  Fun .is .oper .Mu _ .↓ .f-el (tr12 × tr23) .n-ob a =
    B .Mu _ .f-el (tr12 .n-ob a × tr23 .n-ob a)
  Fun .is .oper .Mu _ .↓ .f-el (tr12 × tr23) .n-hom-fw _ hom =
    Hom|Hom-Mu B _ _ _ (tr12 .n-hom-fw _ hom × tr23 .n-hom-fw _ hom )
  Fun .is .oper .Mu _ .↓ .f-el (tr12 × tr23) .n-hom-bw _ hom =
    Hom-Mu|Hom B _ _ _ (tr12 .n-hom-bw _ hom × tr23 .n-hom-bw _ hom )
  Fun .is .oper .Mu _ .↓ .f-to _ (to12 × to23) .↓ a =
    B .Mu _ .f-to _ (to12 .↓ a × to23 .↓ a)
  Fun .is .prop .assoc-fw _ (tr12 × tr23 × tr34) .↓ a =
    B .assoc-fw _ (tr12 .n-ob a × tr23 .n-ob a × tr34 .n-ob a)
  Fun .is .prop .assoc-bw _ (tr12 × tr23 × tr34) .↓ a =
    B .assoc-bw _ (tr12 .n-ob a × tr23 .n-ob a × tr34 .n-ob a)
  Fun .is .prop .lunit-fw _ tr12 .↓ a = B .lunit-fw _ (tr12 .n-ob a)
  Fun .is .prop .lunit-bw _ tr12 .↓ a = B .lunit-bw _ (tr12 .n-ob a)
  Fun .is .prop .runit-fw _ tr12 .↓ a = B .runit-fw _ (tr12 .n-ob a)
  Fun .is .prop .runit-bw _ tr12 .↓ a = B .runit-bw _ (tr12 .n-ob a)
  Fun .is .prop .bunit-fw _ .↓ a = B .bunit-fw _
  Fun .is .prop .bunit-bw _ .↓ a = B .bunit-bw _
