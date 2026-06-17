open import 0-Dim.!quali
open import 1-Dim.Set.Def-Types
open import 1-Dim.Set.Def-Opers.Fun
open import 1-Dim.Set.Def-Opers.Fun-To
open import 2-Dim.Quiver.Def-Types-pub
import 2-Dim.Cat.Def-Types.Obj as Cat
open import 2-Dim.Cat.Def-Types-pub.Ob

module 1-Dim.Set.Extra.SetC where

Fun:C : Cat.[Ob]
Fun:C .It = Fun.Quiver
Fun:C .oper = Fun.oper
Fun:C .prop = Fun.prop

-- TODO
-- with Unit isTerm
-- with Void isInit
-- with Prod isProd
-- with Summ isSumm
-- with Exp isExp
