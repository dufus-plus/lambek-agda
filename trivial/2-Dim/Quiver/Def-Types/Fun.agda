open import 0-Dim.!quali
import 1-Dim.AnySet.Def-Types as AnySet
open import 2-Dim.Quiver.Def-Types.Ob
open import 2-Dim.Quiver.Def-Types-pub.Ob

--
-- define (Fun)ctions on (Gra)phs
--
module 2-Dim.Quiver.Def-Types.Fun where

module _ (AB @(A > B) : [2~] [Ob]) where
  module :[Fun] where
    -- function on elements
    :F-Ob = AnySet.[Fun] (A .Ob > B .Ob)
    module _ (F-Ob : :F-Ob) where
      -- function on relations
      :F-Hom = AnySet.[Rel|Fun] _ (F-Ob ~ F-Ob) (A .Hom ~ B .Hom)

  record [Fun] : [Any] where
    constructor ‼
    open :[Fun]
    field F-Ob : :F-Ob
    field F-Hom : :F-Hom F-Ob
