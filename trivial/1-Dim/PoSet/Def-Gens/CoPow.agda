open import 0-Dim.!quali
open import 1-Dim.Graph.!publi
open import 1-Dim.PoSet.Def-Types
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.PoSet.Def-Gens.Objs
open import 1-Dim.PoSet.Def-Opers.Fun
open import 1-Dim.PoSet.Def-Opers.Mod

module 1-Dim.PoSet.Def-Gens.CoPow where

module CoPow where
  module _ (IA @(I × A) : [Any] [×] [Ob]) where
    Inj : (i : I) → [Fun] (A > CoPow IA)
    Inj i .↓ = Graph.CoPow.Inj _ i

  module _ (IA @(I × A) : [Any] [×] [Ob]) where
    Glue : [Fun] (CoPow IA > A)
    Glue .↓ = Graph.CoPow.Glue _

  oper-ob = CoPow

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
