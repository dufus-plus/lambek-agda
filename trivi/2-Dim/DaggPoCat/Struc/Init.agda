import 0-Struct.Base
import 2-Struct.Cat.0-Mor 

module 2-Struct.Cat.0-Prop.Init where

open 0-Struct.Base
open 2-Struct.Cat.0-Mor 

module _ {C : [Obj]} (I : C .[Ob]) where
  module :is-Init where

    :Ob>Mr = (ob : C .[Ob]) → C .[Mr] I ob

    module _ (Ob>Mr : :Ob>Mr) where

      :Mr>Tri-fw =
        {ob1 ob2 : C. [Ob]} → (f : C .[Mr] ob1 ob2) → 
        C .[To] (C .Mu (Ob>Mr ob1) f) (Ob>Mr ob2)
      :Mr>Tri-bw =
        {ob1 ob2 : C. [Ob]} → (f : C .[Mr] ob1 ob2) → 
        C .[To] (Ob>Mr ob2) (C .Mu (Ob>Mr ob1) f)
      
      :ToId-fw = C .[To] (Ob>Mr I) (C .Id I)  
      :ToId-bw = C .[To] (C .Id I) (Ob>Mr I)  
  --

  record [is-Init] : Type where
    constructor !
    open :is-Init
    field Ob>Mr : :Ob>Mr      
    field Mr>Tri-fw : :Mr>Tri-fw Ob>Mr
    field Mr>Tri-bw : :Mr>Tri-bw Ob>Mr
    field ToId-fw : :ToId-fw Ob>Mr
    field ToId-bw : :ToId-bw Ob>Mr
  open [is-Init] public
