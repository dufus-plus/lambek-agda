open import 0-Dim
open import 1-Dim.PoSet.Defs
open import 1-Dim.PoSet.Oper
import 2-Dim.PoCat.Defs.Ob as PoCat
import 2-Dim.DblCat.Defs.Ob as DblCat

module 1-Dim.PoSet.Extr.Cat where

open PoCat.[Ob]
open DblCat.[Ob]

Fun:PC : PoCat.[Ob]
Fun:PC .↓ = Fun.Graph
Fun:PC .oper = Fun.oper
Fun:PC .prop = Fun.prop

Mod:PC : PoCat.[Ob]
Mod:PC .↓ = Mod.Graph
Mod:PC .oper = Mod.oper
Mod:PC .prop = Mod.prop

Mod|Fun:DC : DblCat.[Ob]
Mod|Fun:DC .↓ = Mod|Fun.DblGraph
Mod|Fun:DC .V-oper = Mod|Fun.V-oper
Mod|Fun:DC .H-oper = Mod|Fun.H-oper
Mod|Fun:DC .V-prop = Mod|Fun.V-prop
Mod|Fun:DC .H-prop = Mod|Fun.H-prop
Mod|Fun:DC .is = Mod|Fun.is-DblCat
