open import 0-Dim-qua
open import 1-Dim.Graph-pub
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Def-Gens.Objs
open import 1-Dim.PoSet.Def-Opers.Fun
open import 1-Dim.PoSet.Def-Opers.Mod

module 1-Dim.PoSet.Def-Gens.Prod2 where

module Prod2 where
  module _ (AB @(A × B) : [Ob] [×] [Ob]) where
    Prj1 : [Fun] (Prod2 (A × B) > A)
    Prj1 .↓ = Graph.Prod2.Prj1 _
    Prj2 : [Fun] (Prod2 (A × B) > B)
    Prj2 .↓ = Graph.Prod2.Prj2 _

  module _ (X : [Ob]) where
    Diag : [Fun] (X > Prod2 (X × X))
    Diag .↓ = Graph.Prod2.Diag _

  oper-ob = Prod2

  module _ (22ob @ ((A × B) ~ (A' × B')) : [2~] [2×] [Ob]) where
    Prod2-Fun : [2Fun] ((Fun (A > A') × Fun (B > B')) > Fun (Prod2 (A × B) > Prod2 (A' × B')))
    Prod2-Fun .↓ .f-ob (fa × fb) .↓ .f-ob (a × b) = fa .f-ob a × fb .f-ob b
    Prod2-Fun .↓ .f-ob (fa × fb) .↓ .f-to _ (ato × bto) = fa .f-to _ ato × fb .f-to _ bto
    Prod2-Fun .↓ .f-to _ (fato × fbto) .↓ (a × b) = fato .↓ a × fbto .↓ b

    Prod2-Mod : [2Fun] ((Mod (A ~ A') × Mod (B ~ B')) > Mod (Prod2 (A × B) ~ Prod2 (A' × B')))
    Prod2-Mod .↓ .f-ob (Ma × Mb) .It .M-ob ((a × b) ~ (a' × b')) =
      Any.Prod2 (Ma .M-ob (a ~ a') × Mb .M-ob (b ~ b'))
    Prod2-Mod .↓ .f-ob (Ma × Mb) .is .lact _ ((ato × bto) × (ma × mb)) =
      Ma .lact _ (ato × ma) × Mb .lact _ (bto × mb)
    Prod2-Mod .↓ .f-ob (Ma × Mb) .is .ract _ ((ma × mb) × (ato × bto)) =
      Ma .ract _ (ma × ato) × Mb .ract _ (mb × bto)
    Prod2-Mod .↓ .f-to _ (maf × mbf) .↓ _ (ma × mb) = maf .↓ _ ma × mbf .↓ _ mb

    -- TODO [Mod|Fun]
