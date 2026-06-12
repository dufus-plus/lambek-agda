open import 0-Dim
open import 1-Dim.Graph.Def-Types.Ob
open import 1-Dim.Graph.Def-Types.Fun
open import 1-Dim.Graph.Def-Types.Mod

module 1-Dim.Graph.Def-Types.Mod|Fun where

module _ (22A : [22~] [Ob])
         (2VF @(VF1 ~ VF2) : Any.[Dup|R] (2~ [Fun]) 22A)
         (2HM @(HM1 ~ HM2) : Any.[R|Dup] (2~ [Mod]) 22A) where
  open [Fun]
  open [Mod]

  :Mod|Fun : [Any]
  :Mod|Fun = Any.[Rel|Fun] _ (VF1 .f-ob ~ VF2 .f-ob) (HM1 .M-ob ~ HM2 .M-ob)

  record [Mod|Fun] : [Any] where
    constructor ↑
    field ↓ : :Mod|Fun
