open import 0-Dim
import 1-Dim.AnyPoSet.Defs as AnyPoSet
open import 2-Dim.PoSet-Graph.Defs.Ob

--
-- define (Fun)ctions on (Gra)phs
--
module 2-Dim.PoSet-Graph.Defs.Fun where

module _ (AB @(A > B) : [2~] [Ob]) where
  module :[Fun] where
    open [Ob]
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
