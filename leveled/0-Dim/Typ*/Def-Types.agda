open import 0-Dim.Prelude

module 0-Dim.Typ*.Def-Types where

[#Ob] = [#Typ]
module _ (#O : [#Ob]) where
  [Ob*] = [Typ*] #O

module _ (2# @(#A ~ #B) : [2~] [#Ob]) where
  [#Rel] = 0% [^] ((#A .[%] [~] #B .[%]) → [%Typ])

module _ {2# @(#A ~ #B) : [2~] [#Ob]}
         (#R @(_ ^ %:): [#Rel] (#A ~ #B))
         (2O @(A: ~ B:) : ([2~]* [Ob*]) 2#) where
  [Rel] = ∀ %ab %r → (A: :[~]: B:) %ab → [Typ:] (%: %r %ab)
