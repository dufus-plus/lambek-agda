open import 0-Dim
import 1-Dim.AnyPoSet.Defs as AnyPoSet
import 1-Dim.PoSet.Defs as PoSet
open import 2-Dim.PoSet-DblGra.Defs.PoSet-DblGra-Ob
open import 2-Dim.PoCat.Defs.PoCat-Ob

--
-- (Ob)jects of 2-equipment of 1-(Equip)ment
--
module 2-Dim.Equip.Defs.Equip-Ob where

open import 2-Dim.Equip.Defs.is-Equip public

record [Equip] : [Any] where
  constructor ‼

  -- underlying graph
  field ↓ : [PoSet-DblGra]

  -- operations
  field V-oper : [oper-PoCat] (V-Gra ↓)
  field H-oper : [oper-PoCat] (H-Gra ↓)

  -- properties
  field V-prop : [prop-PoCat] _ V-oper
  field H-prop : [prop-PoCat] _ H-oper

  -- square 2-morphisms operations
  field is : [is-Equip] ↓ V-oper H-oper
  open [is-Equip] is
open [Equip] public
