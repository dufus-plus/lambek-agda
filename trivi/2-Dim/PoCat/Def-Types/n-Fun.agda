open import 0-Dim.!quali
open import 2-Dim.PoCat.Def-Types.Obj
open import 2-Dim.PoCat.Def-Types-pub.Obj
open import 2-Dim.PoCat.Def-Types.Fun
open import 2-Dim.PoCat.Def-Gens.Objs

module 2-Dim.PoCat.Def-Types.n-Fun where

[0-Fun] : Any.[0-Rel] (! ~ [Obj])
[0-Fun] (! ~ B) = B .Ob

[2-Fun] : Any.[2-Rel] (([Obj] × [Obj]) ~ [Obj])
[2-Fun] (2A ~ B) = [Fun] (Prod2 2A ~ B)
