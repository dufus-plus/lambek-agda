open import 0-Dim
open import 1-Dim.PoSet.Gens.Const
open import 1-Dim.PoSet.Gens.Prop
open import 1-Dim.PoSet.Obj-Types

module 1-Dim.PoSet.Gen-Objs.Prop where

module Prop where

  has-Top : [has-Top] Prop
  has-Top .oper = Const _ Any.Unit
