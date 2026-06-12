open import 0-Dim

--
-- define (Set)oids
--
module 1-Dim.Set where

-- export qualified
module Set where
  open import 1-Dim.Set.Defs public
  open import 1-Dim.Set.Oper public
  open import 1-Dim.Set.Gens public

-- re-export records un-qualified
open Set using (‼; [Set]; module [Set]) public
open [Set] public
open Set.[Fun] public
open Set.[Mod] public
open Set.Fun-[To] public
open Set.Mod-[Fun] public
open Set.[Fun|Fun] public
open Set.[Mod|Fun] public
