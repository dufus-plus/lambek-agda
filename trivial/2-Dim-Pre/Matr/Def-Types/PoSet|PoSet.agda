open import 0-Dim.!quali
open import 2-Dim-Pre.Matr.Def-Types.Ob
open import 2-Dim-Pre.Matr.Def-Types.PoSet
open import 2-Dim-Pre.Matr.Def-Types.Graph|Graph
import 1-Dim.PoSet.Def-Types as PoSet
open import 1-Dim.PoSet.Def-Types-pub

--
-- define enriched (Rel)ations between [Any]
--
module 2-Dim-Pre.Matr.Def-Types.PoSet|PoSet where

--
-- square 2-module between V&H posetoids
--
module _ (22O @((A11 ~ A12) ~ (A21 ~ A22)) : [22~] [Ob])
         (2VR @(VR1 ~ VR2) : [Dup|PoSet] 22O)
         (2HR @(HR1 ~ HR2) : [PoSet|Dup] 22O) where

  module :[PoSet|PoSet] = :[Graph|Graph] 22O (VR1 .PS^It ~ VR2 .PS^It) (HR1 .PS^It ~ HR2 .PS^It)

  record [PoSet|PoSet] : [Any] where
    constructor ‼
    open :[PoSet|PoSet]
    field Sqr : :Sqr
    field H-lact : :H-lact Sqr
    field H-ract : :H-ract Sqr
    field V-lact : :V-lact Sqr
    field V-ract : :V-ract Sqr
