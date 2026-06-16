open import 0-Dim.!quali
import 1-Dim.AnyPoSet.Def-Types as AnyPoSet
import 1-Dim.PoSet.Def-Types as PoSet
import 2-Dim.PoCat.Def-Types.Ob as PoCat
import 2-Dim.DblQuiver.Def-Types.Ob as DblQuiver
open import 2-Dim.DblQuiver.Def-Types-pub.Ob

--
-- (Ob)jects of 2-equipment of Double 1-Categories
--
module 2-Dim.DblCat.Def-Types.Ob where

-- base module
open import 2-Dim.DblCat.Def-Types.is-Ob public

record [Ob] : [Any] where
  constructor ‼

  -- underlying graph
  field It : DblQuiver.[Ob]

  -- cats' operations
  field V-oper : PoCat.[oper] (V-Graph It)
  field H-oper : PoCat.[oper] (H-Graph It)

  -- cats' properties
  field V-prop : PoCat.[prop] _ V-oper
  field H-prop : PoCat.[prop] _ H-oper

  -- square 2-morphisms operations
  field is : [is-Ob] It V-oper H-oper
  open [is-Ob] is
