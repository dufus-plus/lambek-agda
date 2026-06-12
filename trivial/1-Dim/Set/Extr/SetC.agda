open import 0-Dim
open import 1-Dim.Set.Defs
open import 1-Dim.Set.Oper
open import 2-Dim.Set-Gra.Defs.Set-Gra-Ob
open import 2-Dim.Cat.Defs.is-Cat
open import 2-Dim.Cat.Defs.Cat-Ob
  using ([Cat]; module [Cat];
         [prop-Cat]; module [prop-Cat])

module 1-Dim.Set.Extr.SetC where

open [Cat]
open [prop-Cat]

SetC : [Cat]
SetC .↓ .Ob  = [Ob]
SetC .↓ .Hom = Fun
SetC .oper .Id  = Fun-Id
SetC .oper .Mu  = Fun-Mu
SetC .prop .Mu-Assoc-fw = Fun.Mu-Assoc-fw
SetC .prop .Mu-Assoc-bw = Fun.Mu-Assoc-bw
SetC .prop .Id-LUnit-fw = Fun.Id-LUnit-fw
SetC .prop .Id-LUnit-bw = Fun.Id-LUnit-bw
SetC .prop .Id-RUnit-fw = Fun.Id-RUnit-fw
SetC .prop .Id-RUnit-bw = Fun.Id-RUnit-bw

-- TODO
-- with Unit isTerm
-- with Void isInit
-- with Prod isProd
-- with Summ isSumm
-- with Exp isExp
