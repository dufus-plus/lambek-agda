open import 0-Dim.!quali
import 1-Dim.Graph.Def-Types as Graph
import 1-Dim.PoSet.Def-Types as PoSet

module 1-Dim.Graph.Conv.From-PoSet where

module From-PoSet where
  Ob : PoSet.[Ob] → Graph.[Ob]
  Ob = PoSet.[Ob].It

  module _ (2A @(A > B) : [2~] PoSet.[Ob]) where
    Fun : PoSet.[Fun] (A > B) → Graph.[Fun] (Ob A > Ob B)
    Fun = PoSet.[Fun].↓

    Mod : PoSet.[Mod] (A > B) → Graph.[Mod] (Ob A > Ob B)
    Mod = PoSet.[Mod].It

    module _ (2M @(MA > MB) : [2~] PoSet.[Mod] (A > B)) where
      Mod-Fun : PoSet.Mod-[Fun] _ (MA > MB) → Graph.Mod-[Fun] _ (Mod MA > Mod MB)
      Mod-Fun m-f = Graph.↑ (PoSet.Mod-[Fun].↓ m-f)

  module _ (22A : [22~] PoSet.[Ob])
           (2VF @(VF1 ~ VF2) : Any.[Dup|R] (2~ PoSet.[Fun]) 22A)
           (2HM @(HM1 ~ HM2) : Any.[R|Dup] (2~ PoSet.[Mod]) 22A) where
    Mod|Fun : PoSet.[Mod|Fun] _ 2VF 2HM →
      Graph.[Mod|Fun] _ (Fun _ VF1 ~ Fun _ VF2) (Mod _ HM1 ~ Mod _ HM2)
    Mod|Fun m|f = Graph.↑ (PoSet.[Mod|Fun].↓ m|f)
