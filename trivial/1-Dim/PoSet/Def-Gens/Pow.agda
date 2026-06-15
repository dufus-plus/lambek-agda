open import 0-Dim
open import 1-Dim.Graph-pub
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Gens.Objs
open import 1-Dim.PoSet.Gens.Fun
open import 1-Dim.PoSet.Gens.Mod

module 1-Dim.PoSet.Gens.Pow where

module Pow where
  module _ (IA @(I > A) : [Any] [~] [Ob]) where
    Prj : (i : I) → [Fun] (Pow IA > A)
    Prj i .↓ = Graph.Pow.Prj _ i

  module _ (IA @(I > A) : [Any] [~] [Ob]) where
    Diag : [Fun] (A > Pow IA)
    Diag .↓ = Graph.Pow.Diag _

  oper-ob = Pow

  -- module _ (22ob @ ((A × B) ~ (A' × B')) : [2~] [2×] [Ob]) where
  --   Prod-Fun : [2Fun] ((Fun (A > A') × Fun (B > B')) > Fun (Prod (A × B) > Prod (A' × B')))
  --   Prod-Fun .↓ .f-ob (fa × fb) .↓ .f-ob (a × b) = fa .f-ob a × fb .f-ob b
  --   Prod-Fun .↓ .f-ob (fa × fb) .↓ .f-to _ (ato × bto) = fa .f-to _ ato × fb .f-to _ bto
  --   Prod-Fun .↓ .f-to _ (fato × fbto) .↓ (a × b) = fato .↓ a × fbto .↓ b

  --   Prod-Mod : [2Fun] ((Mod (A ~ A') × Mod (B ~ B')) > Mod (Prod (A × B) ~ Prod (A' × B')))
  --   Prod-Mod .↓ .f-ob (Ma × Mb) .↓ .M-ob ((a × b) ~ (a' × b')) =
  --     Any.Prod (Ma .M-ob (a ~ a') × Mb .M-ob (b ~ b'))
  --   Prod-Mod .↓ .f-ob (Ma × Mb) .is .lact _ ((ato × bto) × (ma × mb)) =
  --     Ma .lact _ (ato × ma) × Mb .lact _ (bto × mb)
  --   Prod-Mod .↓ .f-ob (Ma × Mb) .is .ract _ ((ma × mb) × (ato × bto)) =
  --     Ma .ract _ (ma × ato) × Mb .ract _ (mb × bto)
  --   Prod-Mod .↓ .f-to _ (maf × mbf) .↓ _ (ma × mb) = maf .↓ _ ma × mbf .↓ _ mb
