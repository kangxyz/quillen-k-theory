# Independent review: the actual acyclic-to-homotopy-fiber map

Date: 2026-10-09. Result: **accepted for the frozen canonical-map endpoint**.
No implementation source was changed.

## Exact input and maps

For arbitrary independent object/hom universes, the sole structural input is
`N : NestedWeakEquivalences V`: two genuine Waldhausen structures with equal
cofibration classes and chosen zeros, and inclusion of the fine weak class into
the coarse one. The domain is the previously constructed actual coarse-acyclic
full subcategory carrying fine weak equivalences.

`changeWeakMap` is the original continuous delooping map of the identity
change-of-weak-class exact functor. `acyclicInclusionMap` is the original
continuous delooping map of the actual inclusion. No replacement maps are used.

The actual zero-to-inclusion natural transformation has component precisely
`N.coarse.isZero.to_ X.obj`. Its pointwise coarse weakness is literally the
object's coarse-acyclicity witness. The proved weak-transformation realization
homotopy is reversed, yielding a homotopy from the composite of those two
original maps to the constant coarse-zero point. The explicit homotopy
constructor keeps that reversed continuous map and changes only its endpoint
proofs. The chosen-zero track is proved constant from the actual shared-zero
equalities and the existing fixed-zero weak-transformation theorem.

`canonicalFiberMap` is the actual path-valued lift into the existing topological
`HomotopyFiber`, whose points have paths from the image of their source point to
the specified coarse basepoint, with the actual compact-open path topology.
The map's path coordinate is exactly the constructed reversed homotopy.
Projection is **definitionally** the original acyclic inclusion. Its chosen
point is the constant-path fiber point over the original fine chosen zero.
Neither path data nor basedness is assumed in the input.

`canonicalFiberKMap N n` is the actual induced map to the fiber's `(n+1)`st
homotopy group. Its projection equals the original public inclusion `KMap`.
This applies to every natural `n`, including the genuine fundamental-group
K₀ definition at `n=0`.

The additional `changeWeak_KMap_comp_acyclic` theorem states that the two original
public K-homomorphisms compose to the trivial homomorphism. Its proof uses actual
K-map composition and weak-transformation invariance with the genuine zero
functor. It establishes the null-composite half only.

## Semantic scope

I read the complete final source, the actual homotopy-fiber path-space/lift
implementation, and the relevant original KMap/basepoint interfaces. No
saturation, all-morphisms-coarse-weak assumption, extension axiom, cylinder,
category-size identification, fiber equivalence, or desired homotopy conclusion
is supplied. All displayed maps, homotopies, paths, and based equalities are
constructed from the stated ordinary nested structures.

This endpoint does **not** assert that the canonical map is a weak equivalence,
that its induced homomorphisms are bijective, that image equals kernel, or that
a Waldhausen fibration/Gillet–Waldhausen theorem has been proved. Those remain
separate mathematical obligations. The accepted theorem gives the precise
original comparison map and its required canonicality data.

## Independent verification

The frozen source was freshly rebuilt in an isolated overlay, using the earlier
independently rebuilt acyclic-subcategory artifact and linked unchanged remaining
dependencies. No production olean was replaced. Lean 4.34.0 ran with `-j1` under
the shared slot1 lock with acquisition logging. The source check was warning-free.

`audits/CanonicalFiberMapIndependentAudit.lean` checks exactly **24 defining-module
origins**, including private/generated declarations. Recursive axiom checks allow
only `propext`, `Classical.choice`, and `Quot.sound`. All origins and all **15
independent consumers** passed warning-free.

The consumers test the actual transformation components and their original
acyclicity witnesses, the original two continuous maps, literal equality with
the reversed weak-transformation homotopy, fixed-zero track, literal path
coordinate, both path endpoint equations, original projection, constant-path
basepoint, the original K-map factorization in every degree and explicitly at
zero, and the original null-composite theorem including pointwise degree-zero
evaluation. They retain independent object/hom universes and add none of the
structural hypotheses excluded above. Frozen hashes match before building,
after building, and after the complete audit.

## Frozen source and evidence

Source: `Quillen/Waldhausen/Fibration/CanonicalFiberMap.lean`

SHA-256: `3b51ce2cb5bf32502918e4e9dc36f6ea1e2ff34d2d8475fd91b9b28dae1e1eb0`

Evidence directory: `logs/canonical-fiber-map-independent-20261009/`.
Its `sources.sha256` manifest has SHA-256
`bd38604e49313f9984ee5aea2872e10b803b95094de050e84e804c5260efe3f7`.

The directory contains the clean `check.log`, fixed24 `audit.log`, fresh
`deps.log`, three source-hash rechecks and `artifacts.sha256` fixing the report,
audit, script, logs and fresh artifact. Build/acquisition records are in
`logs/canonical-fiber-map-independent-session.log` and the audit log itself.
