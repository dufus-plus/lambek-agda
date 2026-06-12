open import 0-Dim
import 1-Dim.AnyPoSet.Defs as AnyPoSet
import 1-Dim.PoSet.Defs as PoSet
import 2-Dim.PoSet-DblGraph.Defs.Ob as PoSet-DblGraph
import 2-Dim.PoCat.Defs.Ob as PoCat

--
-- (Ob)jects of 2-equipment of Double 1-Categories
--
module 2-Dim.DblCat.Defs.Ob where

open import 2-Dim.DblCat.Defs.is public
open PoSet-DblGraph.[Ob]

record [Ob] : [Any] where
  constructor ‼

  -- underlying graph
  field ↓ : PoSet-DblGraph.[Ob]

  -- operations
  field V-oper : PoCat.[oper] (V-Graph ↓)
  field H-oper : PoCat.[oper] (H-Graph ↓)

  -- properties
  field V-prop : PoCat.[prop] _ V-oper
  field H-prop : PoCat.[prop] _ H-oper

  -- square 2-morphisms operations
  field is : [is] ↓ V-oper H-oper
  open [is] is
