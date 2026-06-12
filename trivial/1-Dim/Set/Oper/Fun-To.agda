open import 0-Dim
open import 1-Dim.Set.Defs
open import 1-Dim.Set.Gens.Exp
open import 1-Dim.Set.Oper.Fun
import 2-Dim.Set-Graph.Defs.Ob as Set-Graph
import 2-Dim.Cat.Defs.is as Cat

--
-- Fun-[To] satisfies axioms of [Cat]
--
module 1-Dim.Set.Oper.Fun-To where

open Set-Graph.[Ob]
open Cat.[oper]
open Cat.[prop]
open [Ob]
open Fun-[To]

module Fun where
  Graph : Set-Graph.[Ob]
  Graph .Ob = [Ob] -- PoSet
  Graph .Hom = Fun

  oper : Cat.[oper] Graph
  oper .Id = Fun-Id
  oper .Mu = Fun-Mu

  prop : Cat.[prop] Graph oper
  prop .Mu-Assoc-fw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) .↓ _ = ob4 .refl _
  prop .Mu-Assoc-bw (ob1 ~ ob2 ~ ob3 ~ ob4) (f12 × f23 × f34) .↓ _ = ob4 .refl _
  prop .Id-LUnit-fw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .Id-LUnit-bw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .Id-RUnit-fw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
  prop .Id-RUnit-bw (ob1 ~ ob2) f12 .↓ _ = ob2 .refl _
