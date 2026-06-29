open import 0-Dim.!quali
import 1-Dim.Graph.Def-Types as Graph
import 1-Dim.Set.Def-Types as Set

module 1-Dim.Graph.Conv.From-Set where

module From-Set where
  Ob : Set.[Ob] → Graph.[Ob]
  Ob = Set.[Ob].It

  module _ (2A @(A > B) : [2~] Set.[Ob]) where
    Fun : Set.[Fun] (A > B) → Graph.[Fun] (Ob A > Ob B)
    Fun = Set.[Fun].↓

    Mod : Set.[Mod] (A > B) → Graph.[Mod] (Ob A > Ob B)
    Mod = Set.[Mod].It

    module _ (2M @(MA > MB) : [2~] Set.[Mod] (A > B)) where
      Mod-Fun : Set.Mod-[Fun] _ (MA > MB) → Graph.Mod-[Fun] _ (Mod MA > Mod MB)
      Mod-Fun m-f = Graph.↑ (Set.Mod-[Fun].↓ m-f)

  module _ (22A : [22~] Set.[Ob])
           (2VF @(VF1 ~ VF2) : Any.[Dup|R] (2~ Set.[Fun]) 22A)
           (2HM @(HM1 ~ HM2) : Any.[R|Dup] (2~ Set.[Mod]) 22A) where
    Mod|Fun : Set.[Mod|Fun] _ 2VF 2HM →
      Graph.[Mod|Fun] _ (Fun _ VF1 ~ Fun _ VF2) (Mod _ HM1 ~ Mod _ HM2)
    Mod|Fun m|f = Graph.↑ (Set.[Mod|Fun].↓ m|f)
