open import 0-Dim-qua
open import 1-Dim.Graph.Def-Types
open import 1-Dim.Graph.Def-Types-pub
import 1-Dim.AnyPoSet.Defs as AnyPoSet

module 1-Dim.Graph.Def-Opers.Fun where

module _ (AB : [2~] [Ob]) where
  Fun : [Ob] -- Graph
  Fun .Ob = [Fun] AB
  Fun .To = Fun-[Id] _

Fun-Id : AnyPoSet.Rel-[0Fun] _ (! > Fun)
Fun-Id _ .f-ob = ⑴
Fun-Id _ .f-to _ = ⑴

Fun-Mu : AnyPoSet.Rel-[2Fun] _ ((Fun × Fun) > Fun)
