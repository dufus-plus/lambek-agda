open import 0-Dim.!quali
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Opers
import 2-Dim.PoCat.Def-Types.Obj as PoCat
import 2-Dim.PoCat|PoCat.Def-Types.Obj as PoCat|PoCat
open import 2-Dim.PoCat.Def-Types-pub.Obj
open import 2-Dim.PoCat|PoCat.Def-Types-pub.Obj

module 1-Dim.PoSet.Extra-Defs.as-Cat where

Fun:PC : PoCat.[Obj]
Fun:PC = record { is = Fun.is-Cat }

Mod:PC : PoCat.[Obj]
Mod:PC = record { is = Mod.is-Cat }

Mod|Fun:PC|PC : PoCat|PoCat.[Obj]
Mod|Fun:PC|PC = record { is = Mod|Fun.is-Cat }
