open import 0-Dim.!quali
import 2-Dim-Pre.Matr.Def-Types as Matr
import 1-Dim.PoSet.Def-Types as PoSet
open import 1-Dim.PoSet.Def-Types-pub
import 2-Dim-Pre.PoSet-Qu.Def-Types.Obj as PoSet-Qu
import 2-Dim-Pre.DaggPoSet|Set-Qu.Def-Types.Obj as DaggPoSet|Set-Qu
open import 2-Dim-Pre.DaggPoSet|Set-Qu.Def-Types-pub.Obj
import 2-Dim.PoCat.Def-Types.is-Obj as PoCat

module 2-Dim.DaggPoCat|Cat.Def-Types.is-Obj
  (Ob : [Any])
  (H : PoCat.[is-Obj] Ob) (let module H = PoCat.[is-Obj] H)
  (V : PoCat.[is-Obj] Ob) (let module V = PoCat.[is-Obj] V)
  (H|V : DaggPoSet|Set-Qu.:[Obj].:H|V Ob H.Hom V.Hom)
  (let module H|V = Matr.[DaggPoSet|Set] H|V)
  where

open PoCat using (‼)
open DaggPoSet|Set-Qu using (‼)

module :[is-Obj] where

  -- V&H composition 2-operations

  :H-Id|V : [Any]
  :H|V-Id : [Any]
  :H-Mu|V : [Any]
  :H|V-Mu : [Any]

  :H-Id|V = Any.Rel|Rel-[0₁-Fun] _ _ _ (! ~ H|V.Sqr) (2~ H.Id)
  :H|V-Id = Any.Rel|Rel-[0₂-Fun] _ _ _ (! ~ H|V.Sqr) (2~ V.Id)
  :H-Mu|V = Any.Rel|Rel-[2₁-Fun] _ _ _ ((H|V.Sqr × H|V.Sqr) ~ H|V.Sqr) (2~ H.Mu-el)
  :H|V-Mu = Any.Rel|Rel-[2₂-Fun] _ _ _ ((H|V.Sqr × H|V.Sqr) ~ H|V.Sqr) (2~ V.Mu-el)

  -- goodness property

  :I→H|V : [Any]
  :H→I|V : [Any]
  :H|I→V : [Any]
  :H|V→I : [Any]

  :I→H|V = ∀ 2ob 2V → V.Hom-To 2ob 2V → H|V.Sqr _ 2V (H.Id _ ~ H.Id _)
  :H→I|V = ∀ 2ob 2V → H|V.Sqr _ 2V (H.Id _ ~ H.Id _) → V.Hom-To 2ob 2V
  :H|I→V = ∀ 2ob 2H → H.Hom-To 2ob 2H → H|V.Sqr _ (V.Id _ ~ V.Id _) 2H
  :H|V→I = ∀ 2ob 2H → H|V.Sqr _ (V.Id _ ~ V.Id _) 2H → H.Hom-To 2ob 2H

  -- 2-module's "side-on-square" actions: the code was moved to Matr.[DaggPoSet|Set]

record [is-Obj] : [Any] where
  constructor ‼
  open :[is-Obj]

  -- composites
  field H-Id|V : :H-Id|V
  field H|V-Id : :H|V-Id
  field H-Mu|V : :H-Mu|V
  field H|V-Mu : :H|V-Mu

  -- goodness
  field I→H|V : :I→H|V
  field H→I|V : :H→I|V
  field H|I→V : :H|I→V
  field H|V→I : :H|V→I
