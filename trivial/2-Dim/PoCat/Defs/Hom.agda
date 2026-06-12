open import 0-Dim
import 1-Dim.PoSet.Defs as PoSet
open import 2-Dim.PoCat.Defs.Ob

module 2-Dim.PoCat.Defs.Hom where

open [Ob]
open PoSet.[Ob]
open PoSet.[Fun]

module _ (C : [Ob]) where
  module _ (2ob : [2~] C .Ob) where
    [Hom] = C .Hom 2ob .Ob
    Hom-[To] = C .Hom 2ob .To
  module _ (3ob : [3~] C .Ob) where
    Hom-Mu = C .Mu 3ob .f-ob

  [Dup|Hom] = Any.[Dup|R] (2~ [Hom])
  [Hom|Dup] = Any.[R|Dup] (2~ [Hom])
