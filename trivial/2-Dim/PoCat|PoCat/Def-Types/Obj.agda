open import 0-Dim.!quali
import 2-Dim-Pre.Matr.Def-Types as AnyPoSet
import 1-Dim.PoSet.Def-Types as PoSet
import 2-Dim.PoCat.Def-Types.Obj as PoCat
import 2-Dim-Pre.PoSet|PoSet-Qu.Def-Types.Obj as PoSet|PoSet-Qu

--
-- (Ob)jects of 2-equipment of Double 1-Categories
--
module 2-Dim.PoCat|PoCat.Def-Types.Obj where

open PoCat using (‼)
open PoSet|PoSet-Qu using (‼)

-- base module
open import 2-Dim.PoCat|PoCat.Def-Types.is-Obj public

-- TODO: :[Obj]

module :[Obj] (Ob : [Any]) where
  :V-is = PoCat.[is-Obj] Ob
  :H-is = PoCat.[is-Obj] Ob

  module _ (V-is : :V-is) (let module V = PoCat.[is-Obj] V-is)
           (H-is : :H-is) (let module H = PoCat.[is-Obj] H-is) where
    :H|V = PoSet|PoSet-Qu.:[Obj].:H|V Ob V.Hom H.Hom

record [Obj] : [Any] where
  constructor ‼
  open :[Obj]

  -- data:
  -- underlying graph:
  field Ob   : [Any]
  field V-is : :V-is Ob
  field H-is : :H-is Ob
  field H|V  : :H|V Ob V-is H-is

  -- 2-dim operations:
  field is : [is-Obj] Ob V-is H-is H|V

  -- helpers:
  open PoCat.[is-Obj] V-is public
    using ()
    renaming
    ( Hom      to V-Hom;
      Hom-It   to V-Hom-It;
      Hom-El   to V-Hom-El;
      Hom-To   to V-Hom-To;
      Hom-is   to V-Hom-is;
      Hom-refl to V-Hom-refl;
      Hom-tran to V-Hom-tran;
      oper     to V-oper;
      Id       to V-Id;
      Mu       to V-Mu;
      Mu-el    to V-Mu-el;
      Mu-to    to V-Mu-to;
      prop     to V-prop;
      assoc-fw to V-assoc-fw;
      assoc-bw to V-assoc-bw;
      lunit-fw to V-lunit-fw;
      lunit-bw to V-lunit-bw;
      runit-fw to V-runit-fw;
      runit-bw to V-runit-bw;
      bunit-fw to V-bunit-fw;
      bunit-bw to V-bunit-bw;
      Qu       to V-Qu )

  open PoCat.[is-Obj] H-is public
    using ()
    renaming
    ( Hom      to H-Hom;
      Hom-It   to H-Hom-It;
      Hom-El   to H-Hom-El;
      Hom-To   to H-Hom-To;
      Hom-is   to H-Hom-is;
      Hom-refl to H-Hom-refl;
      Hom-tran to H-Hom-tran;
      oper     to H-oper;
      Id       to H-Id;
      Mu       to H-Mu;
      Mu-el    to H-Mu-el;
      Mu-to    to H-Mu-to;
      prop     to H-prop;
      assoc-fw to H-assoc-fw;
      assoc-bw to H-assoc-bw;
      lunit-fw to H-lunit-fw;
      lunit-bw to H-lunit-bw;
      runit-fw to H-runit-fw;
      runit-bw to H-runit-bw;
      bunit-fw to H-bunit-fw;
      bunit-bw to H-bunit-bw;
      Qu       to H-Qu )

  open Matr.[PoSet|PoSet] H|V public
    using (H-lact; H-ract; V-lact; V-ract)
    renaming (Sqr to H|V-Sqr)

  open [is-Obj] is public

  V-Ob : PoCat.[Obj]
  V-Ob = ‼ Ob V-is
  H-Ob : PoCat.[Obj]
  H-Ob = ‼ Ob H-is

  Qu : PoSet|PoSet-Qu.[Obj]
  Qu = ‼ Ob V-Hom H-Hom H|V
