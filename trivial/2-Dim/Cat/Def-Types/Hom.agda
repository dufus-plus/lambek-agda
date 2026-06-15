open import 0-Dim-qua
import 1-Dim.Set.Def-Types as Set
open import 1-Dim.Set.Def-Types-pub
open import 2-Dim.Cat.Def-Types.Ob
open import 2-Dim.Cat.Def-Types-pub.Ob

module 2-Dim.Cat.Def-Types.Hom where

module _ (C : [Ob]) where
  module _ (2ob : [2~] C .Ob) where
    [Hom] = C .Hom 2ob .Ob
    Hom-[To] = C .Hom 2ob .To
  module _ (3ob : [3~] C .Ob) where
    Hom-Mu = C .Mu 3ob .f-ob

  [Dup|Hom] = Any.[Dup|R] (2~ [Hom])
  [Hom|Dup] = Any.[R|Dup] (2~ [Hom])
