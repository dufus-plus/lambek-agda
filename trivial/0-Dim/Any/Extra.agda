open import 0-Dim-qua
open import 1-Dim.Graph-pub
open import 1-Dim.PoSet.Def-Types.Ob
open import 1-Dim.PoSet.Def-Types-pub.Ob

module 0-Dim.Any.Extra where

-- poset of propositions
Any : [Ob]
Any .↓ .Ob = Any.[Ob]
Any .↓ .To = Any.[Fun]
Any .is .refl = Any.Fun-Id
Any .is .tran = Any.Fun-Mu
