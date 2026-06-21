open import 0-Dim.!quali
open import 1-Dim.PoSet.!publi
open import 1-Dim.Graph.!publi
import 2-Dim-Pre.PoSet-Qu.Def-Types as PoSet-Qu
open import 2-Dim-Pre.PoSet-Qu.Def-Types-pub
import 3-Dim-Pre.2-Matr.Def-Types as 2-Matr
open import 2-Dim.DaggPoCat.Def-Types
open import 2-Dim.DaggPoCat.Def-Types-pub
open import 2-Dim.DaggPoCat.Def-Gens.Objs
open import 2-Dim.DaggPoCat.Def-Gens.Fun
open import 2-Dim.DaggPoCat.Def-Opers.Hom|Hom

module 2-Dim.DaggPoCat.Def-Opers.Fun where

Fun-Id : 2-Matr.DaggPoCat-[0-Fun] _ (! > Fun)
Fun-Id C .f-ob        = Any.Fun-Id _
Fun-Id C .is .f-hom _ = PoSet.Fun-Id _
Fun-Id C .is .f-Id-fw _   = C .Hom _ .refl _
Fun-Id C .is .f-Id-bw _   = C .Hom _ .refl _
Fun-Id C .is .f-Mu-fw _ _ = C .Hom _ .refl _
Fun-Id C .is .f-Mu-bw _ _ = C .Hom _ .refl _

Fun-Mu : 2-Matr.DaggPoCat-[2-Fun] _ ((Fun × Fun) > Fun)
Fun-Mu (A ~ B ~ C) .f-ob (Fab × Fbc) .f-ob = Any.Fun-Mu _ (Fab .f-ob × Fbc .f-ob)
Fun-Mu (A ~ B ~ C) .f-ob (Fab × Fbc) .is .f-hom _ = PoSet.Fun-Mu _ .f-el (Fab .f-hom _ × Fbc .f-hom _)
Fun-Mu (A ~ B ~ C) .f-ob (Fab × Fbc) .is .f-Id-fw _ =
  C .Hom _ .tran _
  ( Fbc .f-hom _ .f-to _ (Fab .f-Id-fw _) ×
    Fbc .f-Id-fw _ )
Fun-Mu (A ~ B ~ C) .f-ob (Fab × Fbc) .is .f-Id-bw _ =
  C .Hom _ .tran _
  ( Fbc .f-Id-bw _ ×
    Fbc .f-hom _ .f-to _ (Fab .f-Id-bw _) )
Fun-Mu (A ~ B ~ C) .f-ob (Fab × Fbc) .is .f-Mu-fw _ (ahom12 × ahom23) =
  C .Hom _ .tran _
  ( Fbc .f-hom _ .f-to _ (Fab .f-Mu-fw _ (ahom12 × ahom23)) ×
    Fbc .f-Mu-fw _ (Fab .f-hom-el _ ahom12 × Fab .f-hom-el _ ahom23) )
Fun-Mu (A ~ B ~ C) .f-ob (Fab × Fbc) .is .f-Mu-bw _ (ahom12 × ahom23) =
  C .Hom _ .tran _
  ( Fbc .f-Mu-bw _ (Fab .f-hom-el _ ahom12 × Fab .f-hom-el _ ahom23) ×
    Fbc .f-hom _ .f-to _ (Fab .f-Mu-bw _ (ahom12 × ahom23)) )
Fun-Mu (A ~ B ~ C) .is .f-hom ((Fab × Fbc) ~ (Gab × Gbc)) .↓ .f-el (tr12 × tr23) .n-ob _ =
  C .Mu-el _
    ( Fbc .f-hom-el _ (tr12 .n-ob _) ×
      tr23 .n-ob (Gab .f-ob _) )
Fun-Mu (A ~ B ~ C) .is .f-hom ((Fab × Fbc) ~ (Gab × Gbc)) .↓ .f-el (tr12 × tr23) .n-hom-fw _ ahom =
  Hom|Hom-Mu C _ _ _
    ( Fun-Hom|Hom _ Fbc _ _ _ (tr12 .n-hom-fw _ ahom) ×
      tr23 .n-hom-fw _ (Gab .f-hom-el _ ahom) )
Fun-Mu (A ~ B ~ C) .is .f-hom ((Fab × Fbc) ~ (Gab × Gbc)) .↓ .f-el (tr12 × tr23) .n-hom-bw _ ahom =
  Hom-Mu|Hom C _ _ _
    ( Fun-Hom|Hom _ Fbc _ _ _ (tr12 .n-hom-bw _ ahom) ×
      tr23 .n-hom-bw _ (Gab .f-hom-el _ ahom) )
Fun-Mu (A ~ B ~ C) .is .f-hom ((Fab × Fbc) ~ (Gab × Gbc)) .↓ .f-to _ (to12 × to23) .↓ a =
  C .Mu _ .f-to _
    ( Fbc .f-hom _ .f-to _ (to12 .↓ a) ×
      to23 .↓ (Gab .f-ob a) )
Fun-Mu (A ~ B ~ C) .is .f-Id-fw (Fab × Fbc) .↓ a =
  C .Hom _ .tran _
    ( C .runit-bw _ (Fbc .f-hom-el _ (B .Id (Fab .f-ob a))) ×
      Fbc .f-Id-fw (Fab .f-ob a) )
Fun-Mu (A ~ B ~ C) .is .f-Id-bw (Fab × Fbc) .↓ a =
  C .Hom _ .tran _
    ( Fbc .f-Id-bw (Fab .f-ob a) ×
      C .runit-fw _ (Fbc .f-hom-el _ (B .Id (Fab .f-ob a))) )
Fun-Mu (A ~ B ~ C) .is .f-Mu-fw
  ((Fab × Fbc) ~ (Gab × Gbc) ~ (Hab × Hbc))
  ((trFGab × trFGbc) × (trGHab × trGHbc)) .↓ a = all
  where
    eq = trFGbc .n-hom-bw _ (trGHab .n-ob a) .↓
    all =
      C .Hom _ .tran _
        (C .Mu _ .f-to _ (Fbc .f-Mu-fw _ (trFGab .n-ob _ × trGHab .n-ob _) × C .Hom _ .refl _) ×
      C .Hom _ .tran _
        ( C .assoc-fw _ (_ × _ × C .Mu-el _ _) ×
      C .Hom _ .tran _
        ( C .Mu _ .f-to _ (C .Hom _ .refl _ × C .assoc-bw _ (_ × _ × _)) ×
      C .Hom _ .tran _
        ( C .Mu _ .f-to _ (C .Hom _ .refl _ × (C .Mu _ .f-to _ (eq × C .Hom _ .refl _))) ×
      C .Hom _ .tran _
        ( C .Mu _ .f-to _ (C .Hom _ .refl _ × C .assoc-fw _ (_ × _ × _)) ×
        ( C .assoc-bw _ (_ × _ × C .Mu-el _ _)
      ) ) ) ) ) )
Fun-Mu (A ~ B ~ C) .is .f-Mu-bw
  ((Fab × Fbc) ~ (Gab × Gbc) ~ (Hab × Hbc))
  ((trFGab × trFGbc) × (trGHab × trGHbc)) .↓ a = all
  where
    eq = trFGbc .n-hom-fw _ (trGHab .n-ob a) .↓
    all =
      C .Hom _ .tran _
        ( C .assoc-fw _ (_ × _ × C .Mu-el _ _) ×
      C .Hom _ .tran _
        ( C .Mu _ .f-to _ (C .Hom _ .refl _ × C .assoc-bw _ (_ × _ × _)) ×
      C .Hom _ .tran _
        ( C .Mu _ .f-to _ (C .Hom _ .refl _ × (C .Mu _ .f-to _ (eq × C .Hom _ .refl _))) ×
      C .Hom _ .tran _
        ( C .Mu _ .f-to _ (C .Hom _ .refl _ × C .assoc-fw _ (_ × _ × _)) ×
      C .Hom _ .tran _
        ( C .assoc-bw _ (_ × _ × C .Mu-el _ _) ×
        (C .Mu _ .f-to _ (Fbc .f-Mu-bw _ (trFGab .n-ob _ × trGHab .n-ob _) × C .Hom _ .refl _)
      ) ) ) ) ) )
