open import 0-Dim

module 1-Dim.PoCls*.Def-Types.Ob where

record [#Ob] : [Typ]₁ where
  constructor ‼
  field %Ob : [2/] [Typ]
  field %To : [2/] [Typ]
  field Ob% : [Slash] %Ob → [%Typ]
  field To% : [Slash] %To → [2~] [Slash] %Ob → [%Typ]
  field tran% : [2×] [Slash] %To → [Slash] %To

module :Ob* (# : [#Ob])where
  open [#Ob] #
  :Ob: = Typ*.[Ob*] (_ ^ Ob%)
  module _ (Ob: : :Ob:) where
    :To: = Typ*.[Rel*] (_ ^ To%) (Ob: ~ Ob:)
    module _ (To: : :To:) where
      [is-tran] =
        (3% : [3~] _) (2%r @(%r12 × %r23) : [2×] _) →
        (3ob @(ob1 ~ ob2 ~ ob3) : ([3~]: Ob:) 3%) →
        (2to : To: %r12 _ (ob1 ~ ob2) [×] To: %r23 _ (ob2 ~ ob3))
        → To: (tran% 2%r) _ (ob1 ~ ob3)

module _ (# : [#Ob]) where
  record [Ob*] : [Typ:ω] where
    constructor ‼
    open :Ob*
    field Ob: : :Ob: #
    field To: : :To: # Ob:
    field tran: : [is-tran] # Ob: To:
