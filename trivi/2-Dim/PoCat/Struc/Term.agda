open import 0-Dim
open import 2-Dim.PoCat.Defs.Ob
open import 2-Dim.PoCat.Defs.Hom
open import 2-Dim.PoCat.Defs.Fun
open import 2-Dim.PoCat.Defs.Fun-Hom
open import 2-Dim.PoCat.Gens.Const
open import 2-Dim.PoCat.Oper.Fun

module 2-Dim.PoCat.Objs.Term where

open [Ob]
open [Fun]
open Fun-[Hom]

module :is-Term (C : [Ob]) (A : C .Ob) where
  :Term = Fun-[Hom] _ (Fun-Id C > Const _ A)
  module _ (Term : :Term) where
    :to-fw = Hom-[To] C _ (Term .n-ob A ~ C .Id A)
    :to-bw = Hom-[To] C _ (C .Id A ~ Term .n-ob A)

record [is-Term] (C : [Ob]) (A : C .Ob) : Any where
  constructor ‼
  open :is-Term C A
  field Term : :Term
  field to-fw : :to-fw Term
  field to-bw : :to-bw Term
