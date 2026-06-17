open import 0-Dim.!quali
open import 1-Dim.Set.Def-Types
open import 1-Dim.Set.Def-Opers.Fun
open import 1-Dim.Set.Def-Opers.Fun-To
open import 1-Dim.Set.Def-Opers.Mod-Fun
open import 2-Dim.Quiver.Def-Types-pub
import 2-Dim.Cat.Def-Types.Obj as Cat
import 2-Dim.PoCat.Def-Types.Obj as PoCat
open import 2-Dim.Cat.Def-Types-pub.Obj
open import 2-Dim.PoCat.Def-Types-pub.Obj

module 1-Dim.Set.Extra-Defs.as-Cat where

Fun:C : Cat.[Obj]
Fun:C .It   = Fun:Q
Fun:C .oper = Fun.oper
Fun:C .prop = Fun.prop

Mod:PC : PoCat.[Obj]
Mod:PC .It   = Mod:PQ
Mod:PC .oper = Mod.oper
Mod:PC .prop = Mod.prop
