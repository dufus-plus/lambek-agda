open import 0-Dim
open import 2-Dim.Cat.Defs.Cat-Ob

module 2-Dim.Cat.Gens.Unit where

Unit : [Cat]

Unit .[Ob] = Any.Unit
Unit .[Mr] _ _ = Any.Unit 
Unit .[To] _ _ = Any.Unit
Unit .Id _ = !
Unit .Mu _ _ = !
Unit .To-Refl _ = !
Unit .To-Symm _ = !
Unit .To-Tran _ _ = !
Unit .Mu-Cong2 _ _ = !
Unit .Mu-CongL _ _ = !
Unit .Mu-CongR _ _ = !
Unit .Mu-Assoc-fw _ _ _ = !
Unit .Mu-Assoc-bw _ _ _ = !
Unit .Id-LUnit-fw _ = !
Unit .Id-LUnit-bw _ = ! 
Unit .Id-RUnit-fw _ = ! 
Unit .Id-RUnit-bw _ = ! 
