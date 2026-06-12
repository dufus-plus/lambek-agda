open import 0-Dim.Prelude

-- formal colimits of formal limits
-- influenced by ind-pro-objects
module 0-Dim.IndPro*.Def-Types where

module _ {%i %j}
    (I : [Typ:] %i) (J : [Typ:] %j) where
  record _[/]_ : [Typ:] (%i ⊔ %j) where
    constructor _/_
    field i : I
    field j : J
  open _[/]_ public

record [#Ob] : [Typ]₁ where
  constructor ‼
  field %I : [Typ]
  field %J : [Typ]
  field IOb% : %I [/] %J → [%Typ]
  field JOb% : %I [/] %J → [%Typ]
  field Elm% : %I [/] %J → [%Typ]

module _ (# : [#Ob]) where
  record [Ob*] : [Typ:ω] where
    constructor ‼
    open [#Ob] #
    field IOb: : [Typ*] ((%I [/] %J) ^ IOb%)
    field JOb: : [Typ*] ((%I [/] %J) ^ JOb%)
    field Elm: : ∀ %ij → (ijob : IOb: %ij [/] JOb: %ij) → [Typ:] (Elm% %ij)

open [#Ob]
open [Ob*]

record [Kit] {#O} (O : [Ob*] #O) : [Typ:ω] where
  constructor ‼
  field k-%i  : #O .%I
  field k-iob: : ∀ %j → O .IOb: (k-%i / %j)
  field k-elm: : ∀ %j → (job : O .JOb: (k-%i / %j)) → O .Elm: _ (k-iob: %j / job)
open [Kit]

private module Exp (2# @(#A ~ #B) : [2~] [#Ob]) where
  Fun#-%I : [Typ]
  Fun#-%I = (#A .%I → #B .%I) [×] (#B .%J → #A .%J)
  Fun#-%J : [Typ]
  Fun#-%J = #A .%I [×] #B .%J
  Fun#-%I/J : [Typ]
  Fun#-%I/J = Fun#-%I [/] Fun#-%J

  module _ (%ij @((fi , fj) / (ai , bj)) : Fun#-%I/J) where
    A-%eval : #A .%I [/] #A .%J
    A-%eval = ai / fj bj
    B-%eval : #B .%I [/] #B .%J
    B-%eval = fi ai / bj
    Fun#-IOb% = #A .IOb% A-%eval ⊔ #B .IOb% B-%eval
              ⊔ #B .JOb% B-%eval ⊔ #A .JOb% A-%eval
    Fun#-JOb% = #A .IOb% A-%eval ⊔ #B .JOb% B-%eval
    Fun#-Elm% = #A .Elm% A-%eval ⊔ #B .Elm% B-%eval

  Fun# : [#Ob]
  Fun# .%I = Fun#-%I
  Fun# .%J = Fun#-%J
  Fun# .IOb% = Fun#-IOb%
  Fun# .JOb% = Fun#-JOb%
  Fun# .Elm% = Fun#-Elm%

  module _ (2O @(A ~ B) : ([2~]* [Ob*]) 2#) where
    Fun : [Ob*] Fun#
    Fun .IOb: %ij =
        (A .IOb: (A-%eval %ij) → B .IOb: (B-%eval %ij)) [×]
        (B .JOb: (B-%eval %ij) → A .JOb: (A-%eval %ij))
    Fun .JOb: %ij = A .IOb: (A-%eval %ij) [×] B .JOb: (B-%eval %ij)
    Fun .Elm: ((fi , fj) / (ai , bj)) ((fiob , fjob) / (aiob , bjob)) =
        A .Elm: _ (aiob / fjob bjob) → B .Elm: _ (fiob aiob / bjob)

Fun# = Exp.Fun#

module _ {2# : [2~] [#Ob]}
         (2O : ([2~]* [Ob*]) 2#) where
  Fun = Exp.Fun 2# 2O

module _ {2# @(#A ~ #B) : [2~] [#Ob]}
         (2O @(A ~ B) : ([2~]* [Ob*]) 2#) where
  app : [Kit] (Fun (A ~ B)) → ([Kit] A → [Kit] B)
  app (‼ (kf-fi% , kf-fj%) kf-iob kf-elm) (‼ ka-%i ka-iob ka-elm) = record where
    k-%i = kf-fi% ka-%i
    k-iob: %bj =
      let (kf-fiob , kf-fjob) = kf-iob (ka-%i , %bj) in
      kf-fiob (ka-iob (kf-fj% %bj))
    k-elm: %bj bjob =
      let (kf-fiob , kf-fjob) = kf-iob (ka-%i , %bj) in
      kf-elm (ka-%i , %bj) (ka-iob (kf-fj% %bj) , bjob)
        (ka-elm (kf-fj% %bj) (kf-fjob bjob))
