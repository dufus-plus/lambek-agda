open import 0-Dim

module 1-Dim.PoClu*.Def-Types.Ob where

module _ (I : [#Typ]) (J : [#Typ]) where
  record _[/]_  : [Typ] where
    constructor _/_
    field i : I .[%]
    field j : J .[%]
  open _[/]_ public

module _ {I : [#Typ]} {J : [#Typ]} where
  /⊔ : I [/] J → [%Typ]
  /⊔ (i / j) = I .%: i ⊔ J .%: j

module _ {I J}
       (I: : [Typ*] I) (J: : [Typ*] J)
       (ij : I [/] J) where
  record _*[/]*_ : [Typ:] (/⊔ ij) where
    constructor _/_
    field i : I: (ij .i)
    field j : J: (ij .j)
  open _*[/]*_ public

record [#Ob] : [Typ]₁ where
  constructor ‼
  field I : [#Typ]
  field J : [#Typ]
  field El% : I [/] J → [%Typ]

module _ (# : [#Ob]) where
  record [Ob*/*] : [Typ:ω] where
    constructor ‼
    open [#Ob] #
    field I: : [Typ*] I
    field J: : [Typ*] J
    field El: : ∀ (%ij) → (ij : (I: *[/]* J:) %ij) → [Typ:] (El% %ij)
