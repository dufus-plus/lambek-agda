open import 0-Dim
import 1-Dim.Graph.Defs.Mod as Graph
open import 1-Dim.Set.Defs.Ob

--
-- define (Mod)ules on (Set)oids
--
module 1-Dim.Set.Defs.Mod where

open import 1-Dim.Set.Defs.is-Mod public

module _ (AB @(A ~ B) : [2~] [Ob]) where
  record [Mod] : [Any] where
    constructor ‼

    field ↓ : :Mod AB
    open Graph.[Mod] ↓ public

    field is : [is-Mod] AB ↓
    open [is-Mod] is public
