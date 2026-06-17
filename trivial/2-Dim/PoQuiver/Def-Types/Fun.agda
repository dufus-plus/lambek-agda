open import 0-Dim.!quali
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet
open import 2-Dim.PoQuiver.Def-Types.Obj
open import 2-Dim.PoQuiver.Def-Types-pub.Obj

--
-- define (Fun)ctions on (Gra)phs
--
module 2-Dim.PoQuiver.Def-Types.Fun where

module _ (AB @(A > B) : [2~] [Obj]) where
  module :[Fun] where
    -- function on elements
    :f-el = AnyPoSet.[Fun] (A .Ob > B .Ob)
    module _ (f-el : :f-el) where
      -- function on relations
      :F-Hom = AnyPoSet.[Rel|Fun] _ (f-el ~ f-el) (A .Hom ~ B .Hom)

  record [Fun] : [Any] where
    constructor ‼
    open :[Fun]
    field f-el : :f-el
    field F-Hom : :F-Hom f-el
