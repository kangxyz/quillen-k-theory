# Genuine two-degree Waldhausen S-grids

Source: `Quillen/Waldhausen/SConstruction/Bisimplicial.lean`.

## Exact interface

`Grid₂ n m` is the actual preorder `Fin (m.len+1) × Interval n`:

- `n` is the S/interval degree;
- `m` is the weak-equivalence/nerve degree.

It is a separate `def` with its explicit preorder instance, so its indexing
category is not replaced by a scoped product-category instance.
`grid₂ t i j hij` is its corresponding object.

`IsSimplex₂ cof weq F` retains the original four genuine conditions, with
independent bounds: zero diagonal objects, cofibration rows, actual quotient
pushout squares in the interval direction, and pointwise weak equivalences
in the nerve direction. Weak equivalences remain the original `weq`; they
are not replaced by isomorphisms or by arbitrary morphisms.

The construction requires only a category and the two morphism predicates.
It has no preadditive, exact-category, abelian, or homotopy-equivalence
hypothesis. For a genuine Waldhausen structure `V`,

```lean
bisimplicialSSet V : SimplexCategoryᵒᵖ ⥤ SSet.{max u v}
```

has **outer S degree** and **inner nerve degree**, with independent object
and hom universes. `bisimplicialSSetOfProperties cof weq` exposes the same
construction before packaging the Waldhausen axioms.

## Reindexing and exact diagonal identification

`gridMap₂ α β` reindexes the interval and nerve directions independently.
Identity, composition, and interchange laws are strict equalities; the
object-coordinate formula is a `rfl` theorem. `IsSimplex₂.precomp` preserves
all four actual simplex conditions for arbitrary ordinal maps in both
directions, including degeneracies.

`bisimplicialSSetOfProperties_intervalMap_val` and `_nerveMap_val` expose
both bisimplicial maps as actual precomposition with the specified grid
maps. `gridMap₂_diagonal` identifies simultaneous equal reindexing with the
unchanged original `gridMap`.

`bisimplicialDiagonalIso V` is an actual simplicial isomorphism

```lean
TheoremA.diagonalSSet (bisimplicialSSet V) ≅ sSet V.cof V.weq
```

Both directions retain the **identical underlying grid functor** by `rfl`.
The only change is the proof of the equivalent simplex predicates. This
neither changes the public `sSet` definition nor asserts that two unrelated
models have the same homotopy type.

`zeroSimplex₂` is the actual constant zero diagram in both independent
degrees. On the diagonal, the isomorphism sends it to the original
`zeroSimplex` by `rfl`, retaining the chosen zero object exactly.

## Exact-functor postcomposition

`IsSimplex₂.postcomp` takes a genuine structural `IsExact` witness and
preserves all four conditions by actual functor postcomposition. This
statement allows different source/target object and hom universes.

When the simplicial sets occupy the same universe, `bisimplicialSSetMap`
packages these maps into an actual bisimplicial map. Its objectwise formula
is exactly `F.1 ⋙ G`, checked by `rfl`.
`bisimplicialDiagonalIso_naturality` identifies its diagonal with the existing
raw `sSetMap hG`, not a newly defined substitute map.

## Scope

This supplies the genuine two-degree grid model needed for a mixed ordinal
cylinder or additivity deformation. It does not itself construct that
cylinder, prove a simplicial homotopy, prove additivity, or prove
Gillet–Waldhausen. Existing production sources were not modified.

## Verification

The source compiled warning-free with `lean -j1` under
`/tmp/quillen-lean-slot-1.lock`, and an importable olean was produced.
The source-origin audit recursively checks every declaration, including
private/generated constants, and allows only `propext`, `Classical.choice`,
and `Quot.sound`. Its consumers use arbitrary categories with independent
object/hom universes, check both diagonal forward-map formulas and the exact
zero simplex, independent reindexing, different-universe structural
postcomposition, and naturality with the original same-universe S-map.
The final count-fixed audit passed all **68 declaration origins** and every
consumer, without warnings or errors. Only the three standard axioms occur.
The source hash still matches after the audit.

Evidence:

- `logs/waldhausen-bisimplicial-grid.log`
- `audits/WaldhausenBisimplicialAudit.lean`
- `logs/waldhausen-bisimplicial-20261009/sources.sha256`
- `logs/waldhausen-bisimplicial-20261009/origin-axioms-and-consumers.log`

This is the implementing worker's contract and verification report;
independent review is separate.


SHA256:

```text
7a697be609d6f7c4bf9c2c97bbd4f28072d4121fbb322864f57544cd1fba4884  Quillen/Waldhausen/SConstruction/Bisimplicial.lean
ae0f3f6111d01216e9e12944028671793c0bf58038aa482ae0603611a716cb27  audits/WaldhausenBisimplicialAudit.lean
3e26c204627f22072d3d3cea1535c97de08848407a18406e6b689a12bba408a6  logs/waldhausen-bisimplicial-20261009/sources.sha256
ab64d4fb2b303dc674145e7861da3661a1cc4bf2a4da52eb80a42eba7cee94da  logs/waldhausen-bisimplicial-20261009/origin-axioms-and-consumers.log
```
