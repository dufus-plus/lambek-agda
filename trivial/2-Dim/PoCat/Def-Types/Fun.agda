open import 0-Dim.!quali
import 1-Dim.PoSet.Def-Types as PoSet
import 2-Dim-Pre.PoSet-Qu.Def-Types.Fun as PoSet-Qu
open import 2-Dim.PoCat.Def-Types.Obj

module 2-Dim.PoCat.Def-Types.Fun where

open PoSet-Qu using (‼)

module :[Fun] (AB @(A > B) : [2~] [Obj]) where
  open [Obj]
  :f-ob = Any.[Fun] (A .Ob > B .Ob)
  Qu-AB = [Obj].Qu A > [Obj].Qu B

  module :[is-Fun] (f-ob : :f-ob) where
    :f-hom = PoSet-Qu.:[Fun].:f-hom Qu-AB f-ob

    module _ (f-hom : :f-hom) where
      private module f-hom (2ob : _) = PoSet.[Fun] (f-hom 2ob)
      open f-hom
        using ()
        renaming
        ( f-el to f-hom-el;
          f-to to f-hom-to )

      :f-Id-fw =
        (a : A .Ob) →
        B .Hom-To _ (f-hom-el _ (A .Id a) ~ B .Id (f-ob a))
      :f-Id-bw =
        (a : A .Ob) →
        B .Hom-To _ (B .Id (f-ob a) ~ f-hom-el _ (A .Id a))

      :f-Mu-fw =
        (3a @(a1 ~ a2 ~ a3) : [3~] A .Ob) →
        (2hom @(a12 × a23) : A .Hom-El (a1 ~ a2) [×] A .Hom-El (a2 ~ a3)) →
        B .Hom-To _ (f-hom-el _ (A .Mu-el _ 2hom) ~
                    B .Mu-el _ (f-hom-el _ a12 × f-hom-el _ a23))
      :f-Mu-bw =
        (3a @(a1 ~ a2 ~ a3) : [3~] A .Ob) →
        (2hom @(a12 × a23) : A .Hom-El (a1 ~ a2) [×] A .Hom-El (a2 ~ a3)) →
        B .Hom-To _ (B .Mu-el _ (f-hom-el _ a12 × f-hom-el _ a23) ~
                    f-hom-el _ (A .Mu-el _ 2hom))

  record [is-Fun] (f-ob : :f-ob) : [Any] where
    constructor ‼
    open :[is-Fun] f-ob

    --data
    field f-hom   : :f-hom
    field f-Id-fw : :f-Id-fw f-hom
    field f-Id-bw : :f-Id-bw f-hom
    field f-Mu-fw : :f-Mu-fw f-hom
    field f-Mu-bw : :f-Mu-bw f-hom

    -- helper:
    private module f-hom (2ob : _) = PoSet.[Fun] (f-hom 2ob)
    open f-hom public
      using ()
      renaming
      ( f-el to f-hom-el;
        f-to to f-hom-to )

module _ (AB @(A > B) : [2~] [Obj]) where
  record [Fun] : [Any] where
    constructor ‼
    open :[Fun] AB

    -- data:
    field f-ob  : :f-ob
    field is : [is-Fun] f-ob

    -- helper:
    open [is-Fun] is public

open :[Fun] public
  using ([is-Fun]; module :[is-Fun])
