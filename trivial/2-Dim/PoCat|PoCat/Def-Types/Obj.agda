open import 0-Dim.!quali
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet
import 1-Dim.PoSet.Def-Types as PoSet
import 2-Dim.PoCat.Def-Types.Obj as PoCat
import 2-Dim.PoSet|PoSet-Qu.Def-Types.Obj as PoSet|PoSet-Qu

--
-- (Ob)jects of 2-equipment of Double 1-Categories
--
module 2-Dim.PoCat|PoCat.Def-Types.Obj where

open PoCat using (‼)

-- base module
open import 2-Dim.PoCat|PoCat.Def-Types.is-Obj public

record [Obj] : [Any] where
  constructor ‼

  -- underlying graph
  field It : PoSet|PoSet-Qu.[Obj]
  open PoSet|PoSet-Qu.[Obj] It public
    renaming (
      PQ|PQ-V:PQ to PC|PC-V:PQ;
      PQ|PQ-H:PQ to PC|PC-H:PQ
    )

  -- cats' operations
  field V-oper : PoCat.[oper] (PC|PC-V:PQ)
  field H-oper : PoCat.[oper] (PC|PC-H:PQ)

  -- cats' properties
  field V-prop : PoCat.[prop] _ V-oper
  field H-prop : PoCat.[prop] _ H-oper

  PC|PC-V:PC : PoCat.[Obj]
  PC|PC-V:PC = ‼ PC|PC-V:PQ V-oper V-prop
  PC|PC-H:PC : PoCat.[Obj]
  PC|PC-H:PC = ‼ PC|PC-H:PQ H-oper H-prop

  -- square 2-morphisms operations
  field is : [is-Obj] It V-oper H-oper
  open [is-Obj] is public
