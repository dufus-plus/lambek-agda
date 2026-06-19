open import 0-Dim.!quali
import 1-Dim.Set.Def-Types as Set
import 1-Dim.PoSet.Def-Types as PoSet
import 1-Dim.Graph.Def-Types as Graph
open import 1-Dim.Set.Def-Types-pub
open import 1-Dim.PoSet.Def-Types-pub
open import 1-Dim.Graph.Def-Types-pub
open import 1-Dim.PoSet.Conv.Objs

module 1-Dim.PoSet.Conv.From-Set where

module From-Set where
  Ob : Set.[Ob] → PoSet.[Ob]
  Ob = From-Set

  module _ (2O @(A > B) : [2~] Set.[Ob]) where
    Fun : Set.[Fun] (A > B) → PoSet.[Fun] (Ob A > Ob B)
    Fun f .↓ = f .↓

    Mod : Set.[Mod] (A ~ B) → PoSet.[Mod] (Ob A ~ Ob B)
    Mod M .It = M .It
    Mod M .is .lact = M .lact
    Mod M .is .ract = M .ract

    module _ (2f @(f1 ~ f2) : [2~] Set.[Fun] (A > B)) where
      Fun-To : Set.Fun-[To] _ (f1 ~ f2) → PoSet.Fun-[To] _ (Fun f1 ~ Fun f2)
      Fun-To fto .↓ = fto .↓

    module _ (2M @(MA > MB) : [2~] Set.[Mod] (A > B)) where
      Mod-Fun : Set.Mod-[Fun] _ (MA ~ MB) → PoSet.Mod-[Fun] _ (Mod MA ~ Mod MB)
      Mod-Fun m-f .↓ = m-f .↓

  module _ (22O : [22~] Set.[Ob])
           (2VF @(vf1 ~ vf2) : Any.[Dup|R] (2~ Set.[Fun]) 22O)
           (2HM @(HM1 ~ HM2) : Any.[R|Dup] (2~ Set.[Mod]) 22O) where
    Mod|Fun : Set.[Mod|Fun] _ 2VF 2HM →
      PoSet.[Mod|Fun] _ (Fun _ vf1 ~ Fun _ vf2) (Mod _ HM1 ~ Mod _ HM2)
    Mod|Fun m|f .↓ = m|f .↓
