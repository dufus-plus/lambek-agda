open import 0-Dim.!quali
open import 1-Dim.Graph.Def-Types.Ob
open import 1-Dim.Graph.Def-Types-pub.Ob
open import 1-Dim.Graph.Def-Types.Fun
open import 1-Dim.Graph.Def-Gens.Objs

--
-- define (Fun)ctions on (Gra)phs
--
module 1-Dim.Graph.Def-Types.n-Fun where

[0-Fun] : Any.[0-Rel] (! > [Ob])
[0-Fun] (_ > B) = B .El

[2P-Fun] : Any.[2-Rel] ((2× [Ob]) > [Ob])
[2P-Fun] (2A > B) = [Fun] (Prod2 2A > B)

[2T-Fun] : Any.[2-Rel] ((2× [Ob]) > [Ob])
[2T-Fun] (2A > B) = [Fun] (Tens2 2A > B)
