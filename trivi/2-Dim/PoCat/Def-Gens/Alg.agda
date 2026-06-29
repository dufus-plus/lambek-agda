import 0-Struct.Base
import 2-Struct.Cat.0-Mor
import 2-Struct.Cat.1-Mor

module 2-Struct.Cat.0-Oper.Alg where

open 0-Struct.Base
open 2-Struct.Cat.0-Mor
open 2-Struct.Cat.1-Mor

module _ {C : [Obj]} (F : [Fun] C C) where
  
  module Alg-Ob: where
    :It = C .[Ob]
    module _ (It : :It) where
      :Is = C .[Mr] (F .FOb It) It
  --
  record Alg-[Ob] : Type where
    constructor !
    open Alg-Ob:
    field It : :It
    field Is : :Is It 
  open Alg-[Ob]

  module _ (A B : Alg-[Ob]) where
    module Alg-Mr: where
      :mIt = C .[Mr] (A .It) (B .It)
      module _ (mIt : :mIt) where
        :mIs-fw = [Mr|Mr]-fw C (A .Is) (B .Is) (F .FMr mIt) mIt
        :mIs-bw = [Mr|Mr]-bw C (A .Is) (B .Is) (F .FMr mIt) mIt
    --
    record Alg-[Mr] : Type where
      constructor !
      open Alg-Mr:
      field mIt : :mIt
      field mIs-fw : :mIs-fw mIt
      field mIs-bw : :mIs-bw mIt
    open Alg-[Mr] public
  --
 
  open Obj:

  Alg-[To] : :[2-Mor] Alg-[Ob] Alg-[Mr]
  Alg-[To] m m' = C .[To] (m .mIt) (m' .mIt)

  Alg-Id : :Id Alg-[Ob] Alg-[Mr]
  Alg-Id A .mIt = C .Id (A .It)
  Alg-Id A .mIs-fw = res
    where
      --- : [Mr|Mr]-fw C (A .Is) (A .Is) (F .FMr (C .Id (A .It))) (C .Id (A .It)) 
      res : C .[To] (C .Mu (A .Is) (C .Id (A .It))) (C .Mu (F .FMr (C .Id (A .It))) (A .Is))
      sqr : [Mr|Mr]-fw C (A .Is) (A .Is) (C .Id (F .FOb (A .It))) (C .Id (A .It))
      fid : C .[To] (C .Id (F .FOb (A .It))) (F .FMr (C .Id (A .It)))
      fidis : C .[To] (C. Mu (C .Id (F .FOb (A .It))) (A .Is)) 
                      (C .Mu (F .FMr (C .Id (A .It))) (A .Is))
      sqr = [Mr-Id|Mr]-fw C (A .Is)
      fid = F .FId-bw (A .It)
      fidis = C .Mu-CongL fid (A .Is)
      res = C .To-Tran sqr fidis
  Alg-Id A .mIs-bw = res
    where
      --- : [Mr|Mr]-bw C (A .Is) (A .Is) (F .FMr (C .Id (A .It))) (C .Id (A .It)) 
      res : C .[To] (C .Mu (F .FMr (C .Id (A .It))) (A .Is)) (C .Mu (A .Is) (C .Id (A .It)))
      sqr : [Mr|Mr]-bw C (A .Is) (A .Is) (C .Id (F .FOb (A .It))) (C .Id (A .It))
      fid : C .[To] (F .FMr (C .Id (A .It))) (C .Id (F .FOb (A .It)))
      fidis : C .[To] (C .Mu (F .FMr (C .Id (A .It))) (A .Is))
                      (C. Mu (C .Id (F .FOb (A .It))) (A .Is)) 
      sqr = [Mr-Id|Mr]-bw C (A .Is)
      fid = F .FId-fw (A .It)
      fidis = C .Mu-CongL fid (A .Is)
      res = C .To-Tran fidis sqr      

  -- Alg-Id A .mIs-bw = C .To-Refl (A .Is) 

  -- the category of algebras of endofunctor
  Alg : [Obj]

  Alg .[Ob] = Alg-[Ob]
  Alg .[Mr] = Alg-[Mr]
  Alg .[To] = Alg-[To]  
  Alg .Id = Alg-Id

  -- field Id : :Id [Ob] [Mr]
  -- field Mu : :Mu [Ob] [Mr]
  -- field To-Refl : :Refl [Ob] [Mr] [To]
  -- field To-Symm : :Symm [Ob] [Mr] [To]
  -- field To-Tran : :Tran [Ob] [Mr] [To]
  -- field Mu-Cong2 : :Mu-Cong2 [Ob] [Mr] [To] Id Mu
  -- field Mu-CongL : :Mu-CongL [Ob] [Mr] [To] Id Mu
  -- field Mu-CongR : :Mu-CongR [Ob] [Mr] [To] Id Mu
  -- field Mu-Assoc-fw : :Mu-Assoc-fw [Ob] [Mr] [To] Id Mu
  -- field Mu-Assoc-bw : :Mu-Assoc-fw [Ob] [Mr] [To] Id Mu
  -- field Id-LUnit-fw : :Id-LUnit-fw [Ob] [Mr] [To] Id Mu
  -- field Id-LUnit-bw : :Id-LUnit-bw [Ob] [Mr] [To] Id Mu
  -- field Id-RUnit-fw : :Id-RUnit-fw [Ob] [Mr] [To] Id Mu
  -- field Id-RUnit-bw : :Id-RUnit-bw [Ob] [Mr] [To] Id Mu
