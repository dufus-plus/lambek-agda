open import 0-Dim
import 1-Dim.PoSet.Gens.Unit as PoSet
open import 2-Dim.PoCat.Defs.Ob
open import 2-Dim.PoCat.Defs.Fun
open import 2-Dim.PoCat.Gens.Ob
import 2-Dim.PoSet-Graph.Defs.Fun as PoSet-Graph

module 2-Dim.PoCat.Gens.Unit where

module Unit where
  module _ (A : [Ob]) where
    open [Ob]
    open [Fun]
    open [is-Fun]
    open PoSet-Graph.[Fun]

    Term-nOb : [Fun] (A > Unit)
    Term-nOb .↓ .F-Ob = Any.Unit.Term (A .Ob)
    Term-nOb .↓ .F-Hom 2ob = PoSet.Unit.Term-nOb (A .Hom 2ob)
    Term-nOb .is .F-Id-fw _ = !
    Term-nOb .is .F-Id-bw _ = !
    Term-nOb .is .F-Mu-fw _ _ = !
    Term-nOb .is .F-Mu-bw _ _ = !

  Ob = Unit
