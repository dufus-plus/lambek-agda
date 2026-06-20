open import 0-Dim.!quali
import 2-Dim-Pre.AnyPoSet.Def-Types as AnyPoSet
import 1-Dim.PoSet.Def-Types as PoSet
open import 2-Dim-Pre.PoSet-Qu.Def-Types.Obj
open import 2-Dim-Pre.PoSet-Qu.Def-Types-pub.Obj

--
-- define (Fun)ctions on (Gra)phs
--
module 2-Dim-Pre.PoSet-Qu.Def-Types.Fun where

module _ (AB @(A > B) : [2~] [Obj]) where
  module :[Fun] where
    -- function on 0-cells
    :f-ob = AnyPoSet.[Fun] (A .Ob > B .Ob)
    module _ (f-ob : :f-ob) where
      -- function on 1-cells
      :f-hom = AnyPoSet.[Rel|Fun] _ (f-ob ~ f-ob) (A .Hom ~ B .Hom)

  record [Fun] : [Any] where
    constructor ‼
    open :[Fun]

    -- (f)unctions between Graph cells:
    field f-ob : :f-ob
    field f-hom : :f-hom f-ob

    -- helper:
    private module f-hom (2ob : _) = PoSet.[Fun] (f-hom 2ob)
    open f-hom public
      using ()
      renaming
      ( f-el to f-hom-el;
        f-to to f-hom-to )
