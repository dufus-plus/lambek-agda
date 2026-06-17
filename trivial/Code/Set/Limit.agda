open 0-Dim
open 1-Dim
open 2-Dim

module Code.Set.Limit where

module Limit (C : [Cat]) where

  Δ : Cat.[Fun] (Cat.Set > (Cat.Fun (C > Cat.Set)))
  Δ = Cat.Const-Ob (C > Cat.Set)

  LimitF : Cat.[Fun] ((Cat.Fun (C > Cat.Set)) > Cat.Set)
  LimitF .f-el = Limit-Ob

  Adj : Cat.Fun-[Adj] (Δ ~ LimitF)
