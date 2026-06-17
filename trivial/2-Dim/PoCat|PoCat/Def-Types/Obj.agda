open import 0-Dim.!quali
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet
import 1-Dim.PoSet.Def-Types as PoSet
import 2-Dim.PoCat.Def-Types.Obj as PoCat
import 2-Dim.PoQuiver|PoQuiver.Def-Types.Obj as PoQuiver|PoQuiver
open import 2-Dim.PoQuiver|PoQuiver.Def-Types-pub.Obj

--
-- (Ob)jects of 2-equipment of Double 1-Categories
--
module 2-Dim.PoCat|PoCat.Def-Types.Obj where

-- base module
open import 2-Dim.PoCat|PoCat.Def-Types.is-Obj public

record [Obj] : [Any] where
  constructor ‼

  -- underlying graph
  field It : PoQuiver|PoQuiver.[Obj]

  -- cats' operations
  field V-oper : PoCat.[oper] (V-Graph It)
  field H-oper : PoCat.[oper] (H-Graph It)

  -- cats' properties
  field V-prop : PoCat.[prop] _ V-oper
  field H-prop : PoCat.[prop] _ H-oper

  -- square 2-morphisms operations
  field is : [is-Obj] It V-oper H-oper
  open [is-Obj] is
