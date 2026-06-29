open import 0-Dim.Prelude
import 0-Dim.Typ*.Def-Types as Typ*

-- formal colimits of formal limits
-- inspired by ind-pro-object completion
module 0-Dim.LeveledTyp*.Def-Types where

record [#Ob] : [Typ]₁ where
  constructor ‼
  field %I : [Typ]
  field %J : [Typ]
  private %I/J = %I [/] %J
  field Elm% : %I/J → [%Typ]

module _ (2# @(#A ~ #B) : [2~] [#Ob]) where
  private %A~B = (#A .%I [/] #A .%J) [~] (#B .%I [/] #B .%J) where open [#Ob]
  record [#Rel] : [Typ]₁ where
    field %I : [Typ]
    field %J : [Typ]
    private %I/J = %I [/] %J
    field ElmR% : %I/J → %A~B → [%Typ]

module _ (# : [#Ob]) where
  record [Ob*] : [Typ:ω] where
    constructor ‼
    open [#Ob] #
    field Elm: : [Typ*] (_ ^ Elm%)

open [#Ob]
open [Ob*]

record [Kit] {#O} (O : [Ob*] #O) : [Typ:ω] where
  constructor ‼
  field k-%i  : #O .%I
  field k-elm: : ∀ %j → O .Elm: (k-%i / %j)
open [Kit]

module _ (2# @(#A ~ #B) : [2~] [#Ob]) where
  Fun# : [#Ob]
  Fun# .%I = (#A .%I → #B .%I) [×] (#B .%J → #A .%J)
  Fun# .%J = #A .%I [×] #B .%J
  Fun# .Elm% ((fi , fj) / (ai , bj)) =
    #A .Elm% (ai / fj bj) ⊔ #B .Elm% (fi ai / bj)

module _ {2# : [2~] [#Ob]}
         (2O @(A ~ B) : ([2~]* [Ob*]) 2#) where
  Fun : [Ob*] (Fun# 2#)
  Fun .Elm: ((fi , fj) / (ai , bj)) =
      A .Elm: (ai / fj bj) → B .Elm: (fi ai / bj)

  [Fun] : [Typ:ω]
  [Fun] = [Kit] Fun

module _ {2# @(#A ~ #B) : [2~] [#Ob]}
         (2O @(A ~ B) : ([2~]* [Ob*]) 2#) where
  app : [Fun] (A ~ B) → ([Kit] A → [Kit] B)
  app (‼ (fi% , fj%) f-elm) (‼ %a-i a-elm) = record where
    k-%i = fi% %a-i
    k-elm: %b-j = f-elm (%a-i , %b-j) (a-elm (fj% %b-j))

module _ {2# @(#A ~ #B) : [2~] [#Ob]}
         (#R : [#Rel] 2#)
         (2O @(A ~ B) : ([2~]* [Ob*]) 2#) where
  record [Rel] : [Typ:ω] where
    constructor ‼
    open [#Rel] #R
    field ElmR: : Typ*.[Rel] (_ ^ ElmR%) (A .Elm: ~ B .Elm:)
