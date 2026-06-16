open import 0-Dim.!quali
import 1-Dim.Graph.Def-Types.Mod as Graph
open import 1-Dim.Set.Def-Types.Ob

--
-- define (Mod)ules on (Set)oids
--
module 1-Dim.Set.Def-Types.Mod where

open import 1-Dim.Set.Def-Types.is-Mod public

module _ (AB : [2~] [Ob]) where
  record [Mod] : [Any] where
    constructor ‼

    field It : :Mod AB
    open Graph.[Mod] It public

    field is : [is-Mod] AB It
    open [is-Mod] is public
