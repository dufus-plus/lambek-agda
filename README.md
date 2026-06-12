# `Lambek` : WIP roadmap

`Agda` library of sets and cats, and fixpoint encodings in context of sets and cats.

sub-libraries:
- *trivial* - with `type-in-type` Agda option, known for inconsistency
- *leveled* - with `safe` Agda option, not known for inconsistency yet

## 1 - top folders/modules

- 0-Dim : for bare types
- 1-Dim : for setoids, posetoids, classoids, poclassoids;
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

## 5 - fields

### `Set` module

- `[Set]` record with fields:
  - Graph
    - Ob
    - To
  - is-Set
    - refl
    - symm
    - tran
- `[Fun]` record
  - f-Ob
  - f-To
- `[Mod]` record
  - r-Ob
  - r-Ob-LTran
  - r-Ob-RTran
- `[Mod|Fun]` record
  - f-Rel

### `Class` module

- `[Class]` record with fields:
  - Graph
  - is-Class
- `[Fun]`
- and so on

### `Kit` module

- `[Kit]` record
  - k-ob
  - k-to
- `F-Fun` : Class.Fun -> Set.Fun
- `F-Mod` : Class.Mod -> Set.Mod
- `CF-Fun-To` cat-functor
- `CF-Rel-To`
- `EF-Fun|Fun` eqp-functor
- `EF-Rel|Fun`
- `EF-Rel|Rel`

### Cat

- [Cat]
  - `[Ob]`
  - `Hom : AnySet.[Rel] ([Ob] ~ [Ob])`
  - Hom-Id
  - Hom-Mu
  - Hom-Assoc
  - Hom-LUnit
  - Hom-RUnit
- [Fun]
- [Mod]
- [Mod|Fun]
- `AlgC F` construction
- Adjunctions
- isTerm
- isProd
- UnitCat
- ProdCat
- Unit as [Fun]
- Prod as [Fun]
- isExp
- Exp as [Fun]
- isLimit
- hasLimits

### Eqp

- TODO refactor as _internal_ "poset in posets cat/eqp" => cubical 2-Mor
  - see others authors implementations of models of directed type theories (the primary area of interest for equipments in CS)

- `[Eqp]`
  - (!) many-many fields, technically non-manageable
  - (!) how to ensure we have all the fields enlisted
  - (!) how to ensure we have all types tied well without typos
  - we want basic `[Fun]` & `[Rel]` directions, but also derived `[Iso]` and `[Adj]` - so what?
  - [Ob]
  - Ob-Op
  - [Fun]
  - Fun[To]
  - Fun[Eq]
  - Fun-Op
  - Fun-Id
  - Fun-Mu
  - FunTo-Refl
  - FunTo-Tran
  - FunEq-Refl
  - FunEq-Symm
  - FunEq-Tran
  - FunTo-Op
  - FunTo-Mu2
  - FunTo-MuL
  - FunTo-MuR
  - FunEq-Mu2
  - FunEq-MuL
  - FunEq-MuR
  - Fun-Assoc
  - Fun-LUnit
  - Fun-RUnit
  - [Rel]
  - Rel[Fun]
  - Rel[Iso]
  - Rel-Op
  - Rel-Id
  - Rel-Mu
  - RelFun-Refl
  - RelFun-Tran
  - RelIso-Refl
  - RelIso-Symm
  - RelIso-Tran
  - RelFun-Op
  - RelFun-Mu2
  - RelFun-MuL
  - RelFun-MuR
  - RelIso-Mu2
  - RelIso-MuL
  - RelIso-MuR
  - Rel-Assoc
  - Rel-LUnit
  - Rel-RUnit
  - [Rel|Fun]
  - Rel-Op|Fun
  - Rel-Id|Fun
  - Rel-Mu|Fun
  - Rel|Fun-Id
  - Rel|Fun-Mu
  - Rep+ : [Fun] -> [Rel] -- covariant representable, _'companion'_
  - Rep- : [Fun] -> [Rel] -- contravariant representable, _'conjoint'_
  - Rep+Corn(12) - corner 2-mor
  - Rep-Corn(12) - corner 2-mor
  - `[Fun|Fun]` helper for commutative squares
  - FunTo <-> Rel|Fun conv
  - RelTo <-> Rel|Fun conv
  - FunTo <-> Rel|Fun conv
  - RelTo <-> Rel|Fun conv
  - `[Rel|Rel]` (do we need it for higher parametricity?)
  - `[Iso]`, `[Adj]` helper
- `Eqp.[Fun]` type for functor
- eqp of `AlgE F` for eqp-functor `F`

## Roadmap

`TODO`: to coat everything (from **trivial** into **leveled**) with a thin layer of ugly levels of universe

- hope level-indexed construction to make the leveled `Limit` an actual initial object in multi-level universe.
- Q: when the encoding of covariant fixpoint `Barber = Barber -> Prop` breaks levels in the context of Lambek theorem? (Cantor-Russel-Girard-Hurkens paradox)


```agda

  record _[/]_ I J {constructor _/_; field $i : I; $j : J}
  record [#Type] {field $I $J : [Level]}
  [Type*] (! I J %) := (i/j : I [/] J) -> [Type:] (% i/j)

- $[Ob] : [Any]; $[To] : [2~] $[Ob] -> [Any]

- $[Ob] : [ωType]; $[To] : [2~] $[Ob] -> [ωType]
- $[Ob] : [Type]: (% .$Ob); $[To] : [2~] $[Ob] -> [Type]: (% .$To)

- $[Ob]: : [Type*] #.$Ob
- $[To]: : [Rel*] ($[Ob]: ~ $[Ob]:) #.$To

Functors:

Typ.At i/j : [Typ*] #A -> [Typ:] (% i/j)
Cls.At i/j : [Cls*] #A -> [Cls:] (% i/j)
Set.At i/j : [Set*] #A -> [Set:] (% i/j)

Typ.Kit X := Σ i , Π j , X: i/j

Typ.Kit : [Typ*] #A -> [Typ:ω]
Cls.Kit : [Cls*] #A -> [Set:ω]

Cls:C %A : [Cat*] #Cls
Cls*C #A : [Cat:ω]

```
