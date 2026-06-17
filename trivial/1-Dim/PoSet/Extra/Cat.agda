open import 0-Dim.!quali
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Opers
import 2-Dim.PoCat.Def-Types.Obj as PoCat
import 2-Dim.PoCat|PoCat.Def-Types.Obj as DblCat
open import 2-Dim.PoCat.Def-Types-pub.Obj
open import 2-Dim.PoCat|PoCat.Def-Types-pub.Obj

module 1-Dim.PoSet.Extra.Cat where

Fun:PC : PoCat.[Obj]
Fun:PC .It = Fun.Qu
Fun:PC .oper = Fun.oper
Fun:PC .prop = Fun.prop

Mod:PC : PoCat.[Obj]
Mod:PC .It = Mod.Qu
Mod:PC .oper = Mod.oper
Mod:PC .prop = Mod.prop

Mod|Fun:DC : DblCat.[Ob]
Mod|Fun:DC .It = Mod|Fun.Dbl
Mod|Fun:DC .V-oper = Mod|Fun.V-oper
Mod|Fun:DC .H-oper = Mod|Fun.H-oper
Mod|Fun:DC .V-prop = Mod|Fun.V-prop
Mod|Fun:DC .H-prop = Mod|Fun.H-prop
Mod|Fun:DC .is = Mod|Fun.is-DblCat
