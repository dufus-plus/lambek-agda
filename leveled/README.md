# `leveled` sub-library

`Agda` is choosen for its `Setω` feature to deal with large and indexed categories.

Here we supply a kind of ind-pro-completion of the large category of types (and also the same for Setoids, Classoids and Cats) aiming to capture parametricity laws of level-polymorphism. Classoids are local name for non-reflective (aka partial) setoids.

## tree

- `0-Dim` : type-like definitions
  * `Prelude` - common namespace
    - `(i / j) : I [/] J` - named constructor for two kinds of index objects of diagrams in ind-pro-completion
  * `Typ:` - indexed-small category of types at given level
  * `Typ:ω` - very large category of large types (`Agda` feature named `Setω`)
  * `Typ*` - a large category of (I/J)-indexed poly-level types
    - `Kit : Typ* -> Typ:ω` - convert poly-level type into a large type (simple dependent summ-product evaluation)
- `1-Dim:` : setoid-like definitions, indexed-small category of small objects
  * `Cls:` - {symm, tran}, poly-level
  * `Set:` - {refl, symm, tran}, poly-level
  * `PoCls:` - {tran}, poly-level
  * `PoSet:` - {refl, tran}, poly-level
  * `Graph:` - base for above
- `1-Dim:ω` : setoid-like definitions, very large category of large types
  * `Cls:ω` - {symm, tran}, poly-level
  * `Set:ω` - {refl, symm, tran}, poly-level
  * `PoCls:ω` - {tran}, poly-level
  * `PoSet:ω` - {refl, tran}, poly-level
  * `Graph:ω` - base for above
- `1-Dim*` : setoid-like definitions, a large category of indexed poly-level types
  * `Cls*` - {symm, tran}, poly-level
    - `Kit : Cls* -> Set:ω`
  * `Set*` - {refl, symm, tran}, poly-level
  * `PoCls*` - {tran}, poly-level
    - `Kit : PoCls* -> PoSet:ω`
  * `PoSet*` - {refl, tran}, poly-level
  * `Graph*` - base for above
- `2-Dim` : category level
  * `Cat*` - a large 2-category of indexed-small categories (like `Set:`)
  * `Cat:ω` - a very large 2-category of large categories (like `Set*`)
  * `Cat:ω1` - a very-very large 2-category of very large categories (like `Set:ω`)
  * also `Quiver` as base for above
  * also `DblCat`, `Equip` goes here as thin 1-dim versions of higher zoo
- `3-Dim` : higher-dimensional (but hope not needed)
  * `2-Cat` - an (appropriately sized) 3-categories of (sized) 2-categories
- `Applied` : usage of the above framework for applications
  * AdjFunTh for initial object via limit of identity functor
  * Lambek theorem (initial obj is a fixpoint of endofunctor)
  * try to implement (Cantor-Russel)-(Girard-Hurkens) paradox for power-set covariant functor at last.
