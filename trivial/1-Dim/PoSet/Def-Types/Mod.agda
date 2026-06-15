open import 0-Dim-qua
import 1-Dim.Graph.Def-Types.Mod as Graph
open import 1-Dim.PoSet.Def-Types.Ob

--
-- define (Mod)ules on Po(Set)oids
--
module 1-Dim.PoSet.Def-Types.Mod where

open import 1-Dim.PoSet.Def-Types.is-Mod public

module _ (AB @(A ~ B) : [2~] [Ob]) where
  record [Mod] : [Any] where
    constructor ‼

    field It : :Mod AB
    open Graph.[Mod] It public

    field is : [is-Mod] AB It
    open [is-Mod] is public
