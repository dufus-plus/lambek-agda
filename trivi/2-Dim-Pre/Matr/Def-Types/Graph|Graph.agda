open import 0-Dim.!quali
open import 2-Dim-Pre.Matr.Def-Types.Ob
open import 2-Dim-Pre.Matr.Def-Types.Graph
import 1-Dim.Graph.Def-Types as Graph
open import 1-Dim.Graph.Def-Types-pub

--
-- define enriched (Rel)ations between Any
--
module 2-Dim-Pre.Matr.Def-Types.Graph|Graph where

--
-- square 2-module between V&H Graphs
--
module _ (22O @((A11 ~ A12) ~ (A21 ~ A22)) : [22~] [Ob])
         (2VR @(VR1 ~ VR2) : [Dup|Graph] 22O)
         (2HR @(HR1 ~ HR2) : [Graph|Dup] 22O) where

  module :[Graph|Graph] where
    :Sqr = Any.[Rel|Rel] _ (VR1 .G^El ~ VR2 .G^El) (HR1 .G^El ~ HR2 .G^El)

    module _ (H|V-Sqr : :Sqr) where
      -- actions of 2-cells in sides on 2-cells in square

      :H-lact =
        (22ob @((ob11 ~ ob12) ~ (ob21 ~ ob22)): [Dup2|Dup2] 22O) →
        (3v @(v1 ~ v2 ~ v3) :
            VR1 (ob11 ~ ob21) .El [~] VR1 (ob11 ~ ob21) .El [~] VR2 (ob12 ~ ob22) .El)
        (2h @(h1 ~ h2) :
              (HR1 (ob11 ~ ob12) .El) [~] (HR2 (ob21 ~ ob22) .El)) →
        (2hv : VR1 _ .To (v1 ~ v2) [×]
               H|V-Sqr _ (v2 ~ v3) (h1 ~ h2)) →
               H|V-Sqr _ (v1 ~ v3) (h1 ~ h2)

      :H-ract =
        (22ob @((ob11 ~ ob12) ~ (ob21 ~ ob22)): [Dup2|Dup2] 22O) →
        (3v @(v1 ~ v2 ~ v3) :
            VR1 (ob11 ~ ob21) .El [~] VR2 (ob12 ~ ob22) .El [~] VR2 (ob12 ~ ob22) .El)
        (2h @(h1 ~ h2) :
              (HR1 (ob11 ~ ob12) .El) [~] (HR2 (ob21 ~ ob22) .El)) →
        (2hv : H|V-Sqr _ (v1 ~ v2) (h1 ~ h2) [×]
               VR2 _ .To (v2 ~ v3)) →
               H|V-Sqr _ (v1 ~ v3) (h1 ~ h2)

      :V-lact =
        (22ob @((ob11 ~ ob12) ~ (ob21 ~ ob22)): [Dup2|Dup2] 22O) →
        (2v @(v1 ~ v2) :
              (VR1 (ob11 ~ ob21) .El) [~] (VR2 (ob12 ~ ob22) .El)) →
        (3h @(h1 ~ h2 ~ h3) :
            HR1 (ob11 ~ ob12) .El [~] HR1 (ob11 ~ ob12) .El [~] HR2 (ob21 ~ ob22) .El)
        (2HV : HR1 _ .To (h1 ~ h2) [×]
              H|V-Sqr _ (v1 ~ v2) (h2 ~ h3)) →
              H|V-Sqr _ (v1 ~ v2) (h1 ~ h3)

      :V-ract =
        (22ob @((ob11 ~ ob12) ~ (ob21 ~ ob22)): [Dup2|Dup2] 22O) →
        (2v @(v1 ~ v2) :
              (VR1 (ob11 ~ ob21) .El) [~] (VR2 (ob12 ~ ob22) .El)) →
        (3h @(h1 ~ h2 ~ h3) :
            HR1 (ob11 ~ ob12) .El [~] HR2 (ob21 ~ ob22) .El [~] HR2 (ob21 ~ ob22) .El)
        (2hv : H|V-Sqr _ (v1 ~ v2) (h1 ~ h2) [×]
              HR2 _ .To (h2 ~ h3)) →
              H|V-Sqr _ (v1 ~ v2) (h1 ~ h3)

  record [Graph|Graph] : Any where
    constructor ‼
    open :[Graph|Graph]
    field Sqr : :Sqr
    field H-lact : :H-lact Sqr
    field H-ract : :H-ract Sqr
    field V-lact : :V-lact Sqr
    field V-ract : :V-ract Sqr
