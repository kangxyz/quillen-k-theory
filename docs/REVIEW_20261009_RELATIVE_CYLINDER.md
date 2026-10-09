# Independent review: relative complex-cylinder cofibrations

2026-10-09. Lean 4.34.0, mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435`.

## Scope and mathematical verdict

The frozen source under review is
`Quillen/Waldhausen/Cylinder/RelativeComplex.lean`, SHA256
`e5b0428024815beb6dba43cb1367df8cf0cdc9a5d1aa73e11d60b616bf77ec62`.
**Accepted:** the claimed ambient relative degreewise-split cofibration
statements, within the scope below. The exact hypotheses and constructions were inspected,
including the explicit relative-retraction dependency and the underlying
identity-cone factorization. Independent kernel checking is recorded below.

The source proves statements for every abelian category with independent
object and hom universes. It uses actual cochain complexes, actual commutative
squares, actual categorical pushouts, and actual degreewise splittings.
It neither assumes nor concludes a K-equivalence or fibration theorem.

## Actual objects and maps

For an actual chain map `f : K ⟶ L`, the imported cylinder object is
`Cone(𝟙 K) ⊞ L`. The first endpoint is the cone inclusion paired with `f`;
the second is the actual biproduct inclusion of `L`. Their joint map is
`jointInclusion f : K ⊞ L ⟶ middle f`. The actual quotient map is the
biproduct projection onto the cone followed by the cone triangle's arrow
to `K⟦1⟧`. `jointSequenceSplitting f n` gives an explicit splitting of this
short sequence in each degree, without requiring a chain-map retraction.

For a commutative square `α : f ⟶ g`, the new `jointSequenceMap α` retains
exactly these three components:

1. `biprod.map α.left α.right`;
2. `middleFunctor.map α`, the actual cone/biproduct map;
3. `α.left⟦1⟧'`, the actual shifted source map.

Naturality of the two endpoints proves the first square; naturality of the
cone quotient proves the second. Independent consumers check all three
component identities by `rfl`.

## Why the source-only relative hypothesis suffices

`relative_jointInclusion_degreewiseSplitMono` takes the pushout of the
source joint-endpoint inclusion along the map of endpoints. It proves that
the induced map `k` into the target cylinder is degreewise split whenever
**only `α.left`** is degreewise split. The two equations on `k` identify it
with this actual induced map; they do not assume a splitting or a
cofibration conclusion.

This stronger hypothesis is valid because the map of quotient objects of
the joint-endpoint sequences is exactly `α.left⟦1⟧'`. At degree `n`, its
splitting comes from that of `α.left` at degree `n+1`. Evaluation preserves
the actual pushout. The imported
`isSplitMono_relative_of_splittings` constructs an explicit retraction from
the two short-sequence splittings and this quotient-map retraction, and
verifies its identity using pushout extensionality. It does not require a
splitting of the endpoint map or of `α.right`.

`middleFunctor_map_degreewiseSplitMono` does require degreewise splittings
of both `α.left` and `α.right`. Their biproduct map has an explicitly
constructed degreewise retraction. Its pushout is split degreewise; the
subsequent relative map is split by the preceding theorem. The actual
middle-functor map equals the composite by the pushout equation. Thus its
cofibration claim concerns the original functor map, not an isomorphic
replacement or an existentially chosen comparison.

## Limits of acceptance

These are cofibrations in the existing Waldhausen structure on **all**
cochain complexes, whose cofibrations are precisely degreewise split
monomorphisms. The source does not prove membership of the actual relative
quotient in an arbitrary chosen full complex subcategory. It also does not
prove strict zero normalization, assemble a complete cylinder-functor
contract, prove Waldhausen additivity/fibration, or prove Gillet–Waldhausen.
The authored scope document makes the same distinctions. No hidden
conclusion-as-hypothesis or global projectivity assumption was found.

## Independent verification

The reviewed file was freshly compiled to a separate olean overlay with
`lean -j1`, under `/tmp/quillen-lean-slot-1.lock`, without using the author's
olean for this file. Unchanged dependency artifacts are linked into the
overlay; their sources were inspected where relevant and their hashes
recorded. The fresh source check was warning-free. The overlay is placed
first in `LEAN_PATH` for the independent audit, and its import resolution
is logged.

The fixed-count origin audit passed **all 12 declarations**, including
private/generated constants, with recursive dependencies restricted to
`propext`, `Classical.choice`, and `Quot.sound`. Every actual-map identity,
arbitrary-(u,v) consumer, source-only relative endpoint and actual
`splitComplexes` cofibration consumer passed without warnings or errors.
All four recorded source hashes still matched afterward. The import
resolution log explicitly points to the fresh independent review olean.

Evidence directory: `logs/relative-cylinder-independent-20261009/`.
Audit source: `audits/RelativeComplexCylinderIndependentAudit.lean`.

SHA256:

```text
e5b0428024815beb6dba43cb1367df8cf0cdc9a5d1aa73e11d60b616bf77ec62  Quillen/Waldhausen/Cylinder/RelativeComplex.lean
75881190daa61aade3b170b412c2ad17d4bc92c610549d38b6bfacfcffb91ee6  logs/relative-cylinder-independent-20261009/sources.sha256
6165a7dc39d78ecc1fcfeab38066c1018c9a6e1bfc19e48fb6fdadee1efd94f2  audits/RelativeComplexCylinderIndependentAudit.lean
c3bac91e7b01541e3aa978010b5bc0af5f6a4cdc560a6a7caebbb8706474babf  logs/relative-cylinder-independent-20261009/origin-axioms-and-consumers.log
1ecf642a207f6ea1e71ed853980015765840c6dee271d7747ee3b04153012521  logs/relative-cylinder-independent-20261009/import-resolution.log
```

`source-check.log` is empty, documenting the warning-free fresh check;
`post-check-hashes.log` records the four matching sources. No reviewed
production source was modified by this independent review.
