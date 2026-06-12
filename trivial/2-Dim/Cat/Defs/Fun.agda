open import 0-Dim
open import 2-Dim.Cat.Defs.Cat-Ob

module 2-Dim.Cat.Defs.Fun where

module _ (AB @(A > B) : [2~Ob]) where
  module :Fun where
    :F-Ob = Any.[Fun] (A .$Ob > B .$Ob)
    module _ (F-Ob : :F-Ob) where
      :F-Hom = Any.[Rel|Fun] _ (2~ F-Ob) (A .$Hom > B .$Hom)
      module _ (F-Hom : :F-Hom) where
        :F-Hom-To = (2a : [2~] A .$Ob) → 
          Any.[Rel|Fun] _ (2~ F-Hom 2a) (A .$Hom-To _ > B .$Hom-To _)

        :F-Hom-Id-fw = (a : A .$Ob) → 
          B .$Hom-To _ (F-Hom _ (A .$Hom-Id _ (≡ a)) ~ B .$Hom-Id _ (≡ (F-Ob a)) )

  record [Fun] : [Any] where
    constructor ‼
    open :Fun
    field $F-Ob : :F-Ob
    field $F-Hom : :F-Hom $F-Ob
    field $F-Hom-To : :F-Hom-To $F-Ob $F-Hom
  open [Fun] public

