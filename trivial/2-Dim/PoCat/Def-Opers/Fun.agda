open import 0-Dim.!quali
open import 1-Dim.PoSet.!publi
open import 1-Dim.Graph.!publi
import 2-Dim.PoQuiver.Def-Types as PoQuiver
open import 2-Dim.PoQuiver.Def-Types-pub
import 2-Dim.AnyPoCat.Def-Types as AnyPoCat
open import 2-Dim.PoCat.Def-Types
open import 2-Dim.PoCat.Def-Types-pub
open import 2-Dim.PoCat.Def-Gens.Objs
open import 2-Dim.PoCat.Def-Gens.Fun
open import 2-Dim.PoCat.Def-Opers.Hom|Hom

module 2-Dim.PoCat.Def-Opers.Fun where

Fun-Id : AnyPoCat.Rel-[0Fun] _ (! > Fun)
Fun-Id C .It .f-el = Any.Fun-Id _
Fun-Id C .It .F-Hom _ = PoSet.Fun-Id _
Fun-Id C .is .F-Id-fw _ = C .Hom _ .refl _
Fun-Id C .is .F-Id-bw _ = C .Hom _ .refl _
Fun-Id C .is .F-Mu-fw _ _ = C .Hom _ .refl _
Fun-Id C .is .F-Mu-bw _ _ = C .Hom _ .refl _

Fun-Mu : AnyPoCat.Rel-[2Fun] _ ((Fun × Fun) > Fun)
Fun-Mu (A ~ B ~ C) .It .f-el (Fab × Fbc) .It .f-el = Any.Fun-Mu _ (Fab .f-el × Fbc .f-el)
Fun-Mu (A ~ B ~ C) .It .f-el (Fab × Fbc) .It .F-Hom _ = PoSet.Fun-Mu _ .f-el (Fab .F-Hom _ × Fbc .F-Hom _)
Fun-Mu (A ~ B ~ C) .It .f-el (Fab × Fbc) .is .F-Id-fw _ =
  C .Hom _ .tran _
  ( Fbc .F-Hom _ .f-to _ (Fab .F-Id-fw _) ×
    Fbc .F-Id-fw _ )
Fun-Mu (A ~ B ~ C) .It .f-el (Fab × Fbc) .is .F-Id-bw _ =
  C .Hom _ .tran _
  ( Fbc .F-Id-bw _ ×
    Fbc .F-Hom _ .f-to _ (Fab .F-Id-bw _) )
Fun-Mu (A ~ B ~ C) .It .f-el (Fab × Fbc) .is .F-Mu-fw _ (ahom12 × ahom23) =
  C .Hom _ .tran _
  ( Fbc .F-Hom _ .f-to _ (Fab .F-Mu-fw _ (ahom12 × ahom23)) ×
    Fbc .F-Mu-fw _ (Fab .F-Hom _ .f-el ahom12 × Fab .F-Hom _ .f-el ahom23) )
Fun-Mu (A ~ B ~ C) .It .f-el (Fab × Fbc) .is .F-Mu-bw _ (ahom12 × ahom23) =
  C .Hom _ .tran _
  ( Fbc .F-Mu-bw _ (Fab .F-Hom _ .f-el ahom12 × Fab .F-Hom _ .f-el ahom23) ×
    Fbc .F-Hom _ .f-to _ (Fab .F-Mu-bw _ (ahom12 × ahom23)) )
Fun-Mu (A ~ B ~ C) .It .F-Hom ((Fab × Fbc) ~ (Gab × Gbc)) .↓ .f-el (tr12 × tr23) .n-ob _ =
  C .Mu _ .f-el
    ( Fbc .F-Hom _ .f-el (tr12 .n-ob _) ×
      tr23 .n-ob (Gab .f-el _) )
Fun-Mu (A ~ B ~ C) .It .F-Hom ((Fab × Fbc) ~ (Gab × Gbc)) .↓ .f-el (tr12 × tr23) .n-hom-fw _ ahom =
  Hom|Hom-Mu C _ _ _
    ( F-Hom|Hom _ Fbc _ _ _ (tr12 .n-hom-fw _ ahom) ×
      tr23 .n-hom-fw _ (Gab .F-Hom _ .f-el ahom) )
Fun-Mu (A ~ B ~ C) .It .F-Hom ((Fab × Fbc) ~ (Gab × Gbc)) .↓ .f-el (tr12 × tr23) .n-hom-bw _ ahom =
  Hom-Mu|Hom C _ _ _
    ( F-Hom|Hom _ Fbc _ _ _ (tr12 .n-hom-bw _ ahom) ×
      tr23 .n-hom-bw _ (Gab .F-Hom _ .f-el ahom) )
Fun-Mu (A ~ B ~ C) .It .F-Hom ((Fab × Fbc) ~ (Gab × Gbc)) .↓ .f-to _ (to12 × to23) .↓ a =
  C .Mu _ .f-to _
    ( Fbc .F-Hom _ .f-to _ (to12 .↓ a) ×
      to23 .↓ (Gab .f-el a) )
Fun-Mu (A ~ B ~ C) .is .F-Id-fw (Fab × Fbc) .↓ a =
  C .Hom _ .tran _
    ( C .runit-bw _ (Fbc .F-Hom _ .f-el (B .Id (Fab .f-el a))) ×
      Fbc .F-Id-fw (Fab .f-el a) )
Fun-Mu (A ~ B ~ C) .is .F-Id-bw (Fab × Fbc) .↓ a =
  C .Hom _ .tran _
    ( Fbc .F-Id-bw (Fab .f-el a) ×
      C .runit-fw _ (Fbc .F-Hom _ .f-el (B .Id (Fab .f-el a))) )
Fun-Mu (A ~ B ~ C) .is .F-Mu-fw
  ((Fab × Fbc) ~ (Gab × Gbc) ~ (Hab × Hbc))
  ((trFGab × trFGbc) × (trGHab × trGHbc)) .↓ a = all
  where
    eq = trFGbc .n-hom-bw _ (trGHab .n-ob a) .↓
    all =
      C .Hom _ .tran _
        (C .Mu _ .f-to _ (Fbc .F-Mu-fw _ (trFGab .n-ob _ × trGHab .n-ob _) × C .Hom _ .refl _) ×
      C .Hom _ .tran _
        ( C .assoc-fw _ (_ × _ × C .Mu _ .f-el _) ×
      C .Hom _ .tran _
        ( C .Mu _ .f-to _ (C .Hom _ .refl _ × C .assoc-bw _ (_ × _ × _)) ×
      C .Hom _ .tran _
        ( C .Mu _ .f-to _ (C .Hom _ .refl _ × (C .Mu _ .f-to _ (eq × C .Hom _ .refl _))) ×
      C .Hom _ .tran _
        ( C .Mu _ .f-to _ (C .Hom _ .refl _ × C .assoc-fw _ (_ × _ × _)) ×
        ( C .assoc-bw _ (_ × _ × C .Mu _ .f-el _)
      ) ) ) ) ) )
Fun-Mu (A ~ B ~ C) .is .F-Mu-bw
  ((Fab × Fbc) ~ (Gab × Gbc) ~ (Hab × Hbc))
  ((trFGab × trFGbc) × (trGHab × trGHbc)) .↓ a = all
  where
    eq = trFGbc .n-hom-fw _ (trGHab .n-ob a) .↓
    all =
      C .Hom _ .tran _
        ( C .assoc-fw _ (_ × _ × C .Mu _ .f-el _) ×
      C .Hom _ .tran _
        ( C .Mu _ .f-to _ (C .Hom _ .refl _ × C .assoc-bw _ (_ × _ × _)) ×
      C .Hom _ .tran _
        ( C .Mu _ .f-to _ (C .Hom _ .refl _ × (C .Mu _ .f-to _ (eq × C .Hom _ .refl _))) ×
      C .Hom _ .tran _
        ( C .Mu _ .f-to _ (C .Hom _ .refl _ × C .assoc-fw _ (_ × _ × _)) ×
      C .Hom _ .tran _
        ( C .assoc-bw _ (_ × _ × C .Mu _ .f-el _) ×
        (C .Mu _ .f-to _ (Fbc .F-Mu-bw _ (trFGab .n-ob _ × trGHab .n-ob _) × C .Hom _ .refl _)
      ) ) ) ) ) )
