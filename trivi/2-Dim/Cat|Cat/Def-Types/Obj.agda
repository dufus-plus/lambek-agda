open import 0-Dim.!quali
import 2-Dim-Pre.Matr.Def-Types as Matr
import 1-Dim.Set.Def-Types as Set
import 2-Dim.Cat.Def-Types.Obj as Cat
import 2-Dim-Pre.Set|Set-Qu.Def-Types.Obj as Set|Set-Qu

--
-- (Ob)jects of 2-equipment of Double 1-Categories
--
module 2-Dim.Cat|Cat.Def-Types.Obj where

open Cat using (‼)
open Set|Set-Qu using (‼)

-- base module
open import 2-Dim.Cat|Cat.Def-Types.is-Obj public

-- TODO: :[Obj]

module :[Obj] (Ob : Any) where
  :H-is = Cat.[is-Obj] Ob
  :V-is = Cat.[is-Obj] Ob

  module _ (H-is : :H-is) (let module H = Cat.[is-Obj] H-is)
           (V-is : :V-is) (let module V = Cat.[is-Obj] V-is) where
    :H|V = Set|Set-Qu.:[Obj].:H|V Ob H.Hom V.Hom

record [Obj] : Any where
  constructor ‼
  open :[Obj]

  -- data:
  -- underlying graph:
  field Ob   : Any
  field H-is : :H-is Ob
  field V-is : :V-is Ob
  field H|V  : :H|V Ob H-is V-is

  -- 2-dim operations:
  field is : [is-Obj] Ob H-is V-is H|V

  -- helpers:
  open Cat.[is-Obj] H-is public
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
      bunit-bw to H-bunit-bw )

  open Cat.[is-Obj] V-is public
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
      bunit-bw to V-bunit-bw )

  open Matr.[Set|Set] H|V public
    using (H-lact; H-ract; V-lact; V-ract)
    renaming (Sqr to H|V-Sqr)

  open [is-Obj] is public

  H-Ob : Cat.[Obj]
  H-Ob = ‼ Ob H-is
  V-Ob : Cat.[Obj]
  V-Ob = ‼ Ob V-is

  Qu : Set|Set-Qu.[Obj]
  Qu = ‼ Ob H-Hom V-Hom H|V
