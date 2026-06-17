open import 0-Dim.!quali
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Opers
import 2-Dim.PoCat.Def-Types.Obj as PoCat
import 2-Dim.PoCat|PoCat.Def-Types.Obj as PoCat|PoCat
open import 2-Dim.PoCat.Def-Types-pub.Obj
open import 2-Dim.PoCat|PoCat.Def-Types-pub.Obj

module 1-Dim.PoSet.Extra-Defs.as-Cat where

Fun:PC : PoCat.[Obj]
Fun:PC .It = Fun.Qu
Fun:PC .oper = Fun.oper
Fun:PC .prop = Fun.prop

Mod:PC : PoCat.[Obj]
Mod:PC .It = Mod.Qu
Mod:PC .oper = Mod.oper
Mod:PC .prop = Mod.prop

Mod|Fun:PC|PC : PoCat|PoCat.[Obj]
Mod|Fun:PC|PC .It = Mod|Fun:PQ|PQ
Mod|Fun:PC|PC .V-oper = Fun.oper
Mod|Fun:PC|PC .H-oper = Mod.oper
Mod|Fun:PC|PC .V-prop = Fun.prop
Mod|Fun:PC|PC .H-prop = Mod.prop
Mod|Fun:PC|PC .is = Mod|Fun.is-PC|PC
