open import 0-Dim
open import 1-Dim.PoSet
open import 1-Dim.Graph
import 2-Dim.PoSet-Graph.Defs as PoSet-Graph
import 2-Dim.AnyPoCat.Defs as AnyPoCat
open import 2-Dim.PoCat.Defs.Ob
open import 2-Dim.PoCat.Defs.Fun
open import 2-Dim.PoCat.Defs.Fun-Hom
open import 2-Dim.PoCat.Defs.Fun-Hom-To
open import 2-Dim.PoCat.Defs.Hom
open import 2-Dim.PoCat.Defs.Hom|Hom
open import 2-Dim.PoCat.Gens.Ob
open import 2-Dim.PoCat.Gens.Fun
open import 2-Dim.PoCat.Oper.Hom|Hom

module 2-Dim.PoCat.Oper.Fun where

open [Ob]
open [oper]
open [prop]
open [Fun]
open [is-Fun]
open Fun-[Hom]
open Fun-Hom-[To]
open [Hom|Hom]
open PoSet-Graph.[Ob]
open PoSet-Graph.[Fun]
open PoSet.[Ob]
open PoSet.[Fun]
open Graph.[Fun]

Fun-Id : AnyPoCat.Rel-[0Fun] _ (! > Fun)
Fun-Id C .↓ .F-Ob = Any.Fun-Id _
Fun-Id C .↓ .F-Hom _ = PoSet.Fun-Id _
Fun-Id C .is .F-Id-fw _ = C .Hom _ .refl _
Fun-Id C .is .F-Id-bw _ = C .Hom _ .refl _
Fun-Id C .is .F-Mu-fw _ _ = C .Hom _ .refl _
Fun-Id C .is .F-Mu-bw _ _ = C .Hom _ .refl _

Fun-Mu : AnyPoCat.Rel-[2Fun] _ ((Fun × Fun) > Fun)
Fun-Mu (A ~ B ~ C) .↓ .F-Ob (Fab × Fbc) .↓ .F-Ob = Any.Fun-Mu _ (Fab .F-Ob × Fbc .F-Ob)
Fun-Mu (A ~ B ~ C) .↓ .F-Ob (Fab × Fbc) .↓ .F-Hom _ = PoSet.Fun-Mu _ .f-ob (Fab .F-Hom _ × Fbc .F-Hom _)
Fun-Mu (A ~ B ~ C) .↓ .F-Ob (Fab × Fbc) .is .F-Id-fw _ =
  C .Hom _ .tran _
  ( Fbc .F-Hom _ .f-to _ (Fab .F-Id-fw _) ×
    Fbc .F-Id-fw _ )
Fun-Mu (A ~ B ~ C) .↓ .F-Ob (Fab × Fbc) .is .F-Id-bw _ =
  C .Hom _ .tran _
  ( Fbc .F-Id-bw _ ×
    Fbc .F-Hom _ .f-to _ (Fab .F-Id-bw _) )
Fun-Mu (A ~ B ~ C) .↓ .F-Ob (Fab × Fbc) .is .F-Mu-fw _ (ahom12 × ahom23) =
  C .Hom _ .tran _
  ( Fbc .F-Hom _ .f-to _ (Fab .F-Mu-fw _ (ahom12 × ahom23)) ×
    Fbc .F-Mu-fw _ (Fab .F-Hom _ .f-ob ahom12 × Fab .F-Hom _ .f-ob ahom23) )
Fun-Mu (A ~ B ~ C) .↓ .F-Ob (Fab × Fbc) .is .F-Mu-bw _ (ahom12 × ahom23) =
  C .Hom _ .tran _
  ( Fbc .F-Mu-bw _ (Fab .F-Hom _ .f-ob ahom12 × Fab .F-Hom _ .f-ob ahom23) ×
    Fbc .F-Hom _ .f-to _ (Fab .F-Mu-bw _ (ahom12 × ahom23)) )
Fun-Mu (A ~ B ~ C) .↓ .F-Hom ((Fab × Fbc) ~ (Gab × Gbc)) .↓ .f-ob (tr12 × tr23) .n-ob _ =
  C .Mu _ .f-ob
    ( Fbc .F-Hom _ .f-ob (tr12 .n-ob _) ×
      tr23 .n-ob (Gab .F-Ob _) )
Fun-Mu (A ~ B ~ C) .↓ .F-Hom ((Fab × Fbc) ~ (Gab × Gbc)) .↓ .f-ob (tr12 × tr23) .n-hom-fw _ ahom =
  Hom|Hom-Mu C _ _ _
    ( F-Hom|Hom _ Fbc _ _ _ (tr12 .n-hom-fw _ ahom) ×
      tr23 .n-hom-fw _ (Gab .F-Hom _ .f-ob ahom) )
Fun-Mu (A ~ B ~ C) .↓ .F-Hom ((Fab × Fbc) ~ (Gab × Gbc)) .↓ .f-ob (tr12 × tr23) .n-hom-bw _ ahom =
  Hom-Mu|Hom C _ _ _
    ( F-Hom|Hom _ Fbc _ _ _ (tr12 .n-hom-bw _ ahom) ×
      tr23 .n-hom-bw _ (Gab .F-Hom _ .f-ob ahom) )
Fun-Mu (A ~ B ~ C) .↓ .F-Hom ((Fab × Fbc) ~ (Gab × Gbc)) .↓ .f-to _ (to12 × to23) .↓ a =
  C .Mu _ .f-to _
    ( Fbc .F-Hom _ .f-to _ (to12 .↓ a) ×
      to23 .↓ (Gab .F-Ob a) )
Fun-Mu (A ~ B ~ C) .is .F-Id-fw (Fab × Fbc) .↓ a =
  C .Hom _ .tran _
    ( C .RUnit-bw _ (Fbc .F-Hom _ .f-ob (B .Id (Fab .F-Ob a))) ×
      Fbc .F-Id-fw (Fab .F-Ob a) )
Fun-Mu (A ~ B ~ C) .is .F-Id-bw (Fab × Fbc) .↓ a =
  C .Hom _ .tran _
    ( Fbc .F-Id-bw (Fab .F-Ob a) ×
      C .RUnit-fw _ (Fbc .F-Hom _ .f-ob (B .Id (Fab .F-Ob a))) )
Fun-Mu (A ~ B ~ C) .is .F-Mu-fw
  ((Fab × Fbc) ~ (Gab × Gbc) ~ (Hab × Hbc))
  ((trFGab × trFGbc) × (trGHab × trGHbc)) .↓ a = all
  where
    eq = trFGbc .n-hom-bw _ (trGHab .n-ob a) .↓
    all =
      C .Hom _ .tran _
        (C .Mu _ .f-to _ (Fbc .F-Mu-fw _ (trFGab .n-ob _ × trGHab .n-ob _) × C .Hom _ .refl _) ×
      C .Hom _ .tran _
        ( C .Assoc-fw _ (_ × _ × C .Mu _ .f-ob _) ×
      C .Hom _ .tran _
        ( C .Mu _ .f-to _ (C .Hom _ .refl _ × C .Assoc-bw _ (_ × _ × _)) ×
      C .Hom _ .tran _
        ( C .Mu _ .f-to _ (C .Hom _ .refl _ × (C .Mu _ .f-to _ (eq × C .Hom _ .refl _))) ×
      C .Hom _ .tran _
        ( C .Mu _ .f-to _ (C .Hom _ .refl _ × C .Assoc-fw _ (_ × _ × _)) ×
        ( C .Assoc-bw _ (_ × _ × C .Mu _ .f-ob _)
      ) ) ) ) ) )
Fun-Mu (A ~ B ~ C) .is .F-Mu-bw
  ((Fab × Fbc) ~ (Gab × Gbc) ~ (Hab × Hbc))
  ((trFGab × trFGbc) × (trGHab × trGHbc)) .↓ a = all
  where
    eq = trFGbc .n-hom-fw _ (trGHab .n-ob a) .↓
    all =
      C .Hom _ .tran _
        ( C .Assoc-fw _ (_ × _ × C .Mu _ .f-ob _) ×
      C .Hom _ .tran _
        ( C .Mu _ .f-to _ (C .Hom _ .refl _ × C .Assoc-bw _ (_ × _ × _)) ×
      C .Hom _ .tran _
        ( C .Mu _ .f-to _ (C .Hom _ .refl _ × (C .Mu _ .f-to _ (eq × C .Hom _ .refl _))) ×
      C .Hom _ .tran _
        ( C .Mu _ .f-to _ (C .Hom _ .refl _ × C .Assoc-fw _ (_ × _ × _)) ×
      C .Hom _ .tran _
        ( C .Assoc-bw _ (_ × _ × C .Mu _ .f-ob _) ×
        (C .Mu _ .f-to _ (Fbc .F-Mu-bw _ (trFGab .n-ob _ × trGHab .n-ob _) × C .Hom _ .refl _)
      ) ) ) ) ) )
