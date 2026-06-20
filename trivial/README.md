## 1 - top folders/modules

- 0-Dim : for bare types
- 1-Dim : for setoids, posetoids (and classoids, poclassoids)
- 2-Dim : for 1-catoids, 1-equipoid
- 3-Dim : for 2-categories, 2-equipments (but hope not needed)
- Code : define initial object as limit, with application to categories of algebras

## 2 - mid folders/modules

- 0-Dim
  - Prelude : common type definitions (in `[brackets]`)
  - Any : parts of equipment structure on types
- 1-Dim
  - AnySet : Set-enriched relations
  - Set : aka Setoids : with Refl, Symm, Tran
  - PoSet : aka PoSetoids : with Refl, Tran -- "Partially ordered"
  - Class : aka Classoids : with Symm, Tran -- non-reflective
  - PoClass : aka PoClassoids : with Tran -- "Partially ordered" non-reflective
- 2-Dim
  - Cat : 2-equipment of 1-categories
  - PoCat : also locally "Partially ordered" cats
  - Eqp : 2-equipment of 1-equipments
  - (what about `Opposite` in structure?)
- Code
  - `Void := (S : Set) -> S`,
  - `Unit := (S : Set) -> S -> S`
  - reimplement `Prod`, `Nat`
  - "unary product" `Copy(A) := (S : Set) -> (A -> S) -> S` - prove it is isomorphic to identity functor
  - refer to Lambek for `Alg F` for any (cat|eqp)-functor `F`
  - reimplement `Nat`, `List`, `Tree` via functor fixpoint
  - test it for `X -> Prop` fixpoint

## 3 - low folders/modules

- Set, Class - modules for 1-(cat|eqp) of it
  - `Defs` : type definitions
  - `Oper` : internal categorical operations (use types from Cat|Eqp)
  - `Gens` : std generators like Prod, Summ, Exp, Lim, coLim
  - `Extr` : upper-layer wrappers : 1-category of Sets, 1-functor of Prod, etc
- `Kit`
  - more simple module for `Fun`
- Cat, Equip - modules for 2-(cat|eqp) of it
  - Defs, Oper, Gens, Extr
  - internal `[Iso]`
  - `[HardAdj]` vs `[SoftAdj]`
  - types for adjoint (initial, terminal, product, exponential, limit) properties
- `Alg F`
  - implement Lambek theorem for (cat|eqp)

## 4 - files

- Defs : types for cat-minded and equipment-minded morphisms
  - `[Ob]` type
  - `[Fun]`, `[Mod]`, `[Rel]` types
  - globular `Fun-[To]`, `Mod-[To]`, `Rel-[To]` types for cats
  - cubical `[Fun|Fun]`, `[Rel|Fun]`, `[Rel|Rel]` types for eqps
- Oper : identities and compositions
  - Hom-Id, Hom-Mu : for 1-mor
  - Hom-Id|Hom, Hom-Mu|Hom : for cubical 2-mor
  - compose globular and cubical
  - also `Opposite`
- Extr
  - `SetC : [Cat]`
  - `SetE : [Eqp]`
  - `UnitF : Cat.[Fun]` with `Cat.[Adj]`
  - `VoidF : Cat.[Fun]` with `Cat.[Adj]`
  - `ProdF` also
  - 'SummF` also
  - 'ExpF' also
  - 'LimF' also
- Adjs
  - `[HardAdj]` for `[Fun]` in Cat
  - `[SoftAdj]` for `[Rel]` in Eqp
  -  `Rep+`, `Rep-` - _conjoint_ and _companion_ cells in Eqp
  - `[is-Init]`
  - `[is-Term]`
  - `[is-Prod]`
  - `[is-Summ]`
  - `[is-Exp]`
  - `[is-Limit]`
  - maybe also coLimit, coExp, duals in *-autonomous cats
  - _"versatile double limits"_ in equipment (but hope not needed)

## 2-Dim

- Graph-Qu : enriched in Graph, use AnyGraph
- PoSet-Qu : enriched in PoSet, use AnyPoSet
- Set-Quiver : enriched in Set, use AnySet

- PoCat : structure over PoSet-Qu
- Cat : structure over Set-Quiver

- Graph|Graph-Qu : cubical 2-set
- PoSet|PoSet-Qu : both directions is PoSet
- DaggPoSet|Set-Quiver : vertical is dagger PoSet, horizontal is Set

- PoCat|PoCat : p.o. double catoid
- DaggPoCat|Cat : vertical has dagger, horizontal has symmetry
