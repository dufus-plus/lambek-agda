open import 0-Dim-qua
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet
open import 2-Dim.PoQuiver.Def-Types.Ob
open import 2-Dim.PoQuiver.Def-Types-pub.Ob

--
-- define (Fun)ctions on (Gra)phs
--
module 2-Dim.PoQuiver.Def-Types.Fun where

module _ (AB @(A > B) : [2~] [Ob]) where
  module :[Fun] where
    -- function on elements
    :F-Ob = AnyPoSet.[Fun] (A .Ob > B .Ob)
    module _ (F-Ob : :F-Ob) where
      -- function on relations
      :F-Hom = AnyPoSet.[Rel|Fun] _ (F-Ob ~ F-Ob) (A .Hom ~ B .Hom)

  record [Fun] : [Any] where
    constructor ‼
    open :[Fun]
    field F-Ob : :F-Ob
    field F-Hom : :F-Hom F-Ob
