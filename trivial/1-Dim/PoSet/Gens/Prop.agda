open import 0-Dim
open import 1-Dim.Graph-pub
open import 1-Dim.PoSet.Def-Types.Ob
open import 1-Dim.PoSet.Def-Types-pub.Ob

module 1-Dim.PoSet.Gens.Prop where

-- poset of propositions
Prop : [Ob]
Prop .↓ .Ob = Any.[Ob]
Prop .↓ .To = Any.[Fun]
Prop .is .refl = Any.Fun-Id
Prop .is .tran = Any.Fun-Mu

-- poset of relations
module _ (2O @(A ~ B) : [2~] [Any]) where
  Rel : [Ob]
  Rel .↓ .Ob = Any.[Rel] 2O
  Rel .↓ .To = Any.Rel-[Fun] 2O
  Rel .is .refl R _ = ⑴
  Rel .is .tran _ (f12 × f23) ab = (f12 ab) ∘ (f23 ab)
