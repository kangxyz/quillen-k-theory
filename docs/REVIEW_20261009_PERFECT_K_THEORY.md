# Independent review: locally-perfect Waldhausen K-theory

Reviewed 2026-10-09 independently of the implementation author. The frozen
scope is the twenty `Quillen/PerfectComplexes/*.lean` files and ten immediate
`Quillen/Waldhausen/*.lean` files. The active `Waldhausen/QuillenComparison/`
subdirectory is excluded and is not imported by this endpoint. This extends
`REVIEW_20261009_PERFECT_FOUNDATIONS.md`; it includes the coordinator's two
shift/cone closure proofs in `PerfectComplexes/Closure.lean`.

## Accepted mathematical endpoint

For every actual scheme X, `Perfect X` is the full category of sheaf
cochain complexes which, around each point, are isomorphic in the actual
quasi-isomorphism localization to a bounded complex of finite locally free
sheaves. The bound and representative may vary with the point. The
existence of one global strict representative is not an input.

`perfectWaldhausen X` is constructed on this category, with ambient
monomorphisms having locally-perfect quotients as cofibrations and actual
quasi-isomorphisms as weak equivalences. `PerfectK X n` is its genuine
diagonal S-construction realization's (n+1)st based homotopy group. It is
available in every nonnegative degree.

The actual restriction homomorphism, strict-perfect-to-locally-perfect
homomorphism, and degree-zero vector-bundle S-theory homomorphism are
constructed. `PerfectSupportedK j n` uses the actual objects whose
restriction along the specified open immersion j is acyclic; its inclusion
and strict-supported comparison homomorphisms are constructed as well.
No comparison equivalence or localization theorem is an input.

## Semantic proof review

- `LocalHomotopyStep` corrects one component of an approximate homotopy by
  lifting through the epimorphism onto actual cycles. The finite local
  freeness assumption is on that source term only.
- `LocalNullHomotopy` performs a genuinely finite descending induction
  between actual termwise bounds. Each correction may shrink the open;
  the output retains a composite open immersion and a point mapping to the
  originally selected point. It does not intersect infinitely many opens
  or assert global projectivity of vector bundles. Degrees below the bound
  satisfy the homotopy identity because their source objects are zero.
- `LocalQuasiIsoLifting` proves the cone of a quasi-isomorphism acyclic,
  applies the local nullhomotopy theorem, and uses exactness of the actual
  homotopy-category cone triangle. It produces a chain lift up to an
  actual chain homotopy through an arbitrary quasi-isomorphism.
- `DerivedMorphisms` identifies the chosen Gabriel–Zisman localization
  with mathlib's standard derived-category model. The fraction denominator
  is proved quasi-isomorphic, not merely required to be invertible in an
  unrelated category. Cancellation after local lifting gives a chain
  representative of the original derived morphism. The strengthened
  naturality result works for every factorization of actual restriction,
  including the triangulated restriction used later.
- `LocalModels` refines two model neighborhoods by a finite intersection
  and converts arbitrary open-immersion witnesses to actual open subsets
  using the open-image isomorphism. All neighborhood witnesses still
  contain the chosen point.
- `Closure` proves strict shift closure with shifted term bounds and cone
  closure with finite biproduct terms. `LocalTriangles` applies the proved
  local chain representation to the first arrow of a distinguished
  triangle, then uses uniqueness of distinguished cones. `Extension`
  applies this to the inverse rotation of the actual short-exact triangle.
  Thus locally-perfect extension closure is a conclusion, not a field.
- The inherited exact-subcategory adapter proves pushout preservation and
  quasi-isomorphism gluing in the ambient complex category. Zero objects,
  isomorphisms, identities, composition, cofibrancy, existence and stability
  of cofibration pushouts, and gluing are all supplied by proved results.
- The simplices are actual functors from `[n] × Ar[n]` with zero diagonals,
  row cofibrations, quotient pushouts and pointwise weak equivalences in
  the nerve direction. Simultaneous reindexing supplies the diagonal
  simplicial set. Exact functors act by postcomposition and realization.
  The unique zero-object isomorphism rebases these maps to the specified
  zero vertices before taking genuine based homotopy-group homomorphisms.
- Supported extension closure combines the new perfectness theorem with
  exact restriction and the acyclic short-exact-sequence theorem. The
  restricted supported complex is proved quasi-isomorphic to zero, without
  asserting a homotopy-fiber statement.

No semantic correctness blocker was found in this scope.

## Precise exclusions and conventions

The vector-bundle source here is the exact category's Waldhausen S-model,
not the existing public `Scheme.K` Quillen Q-model. Q/S comparison,
Gillet–Waldhausen, strict-versus-locally-perfect equivalences, additivity and
K₀ commutativity, connective localization, and nonconnective spectra remain
separate unproved endpoints. No identification with `Scheme.K` follows
from the constructed comparison maps alone.

The cofibrations reviewed here are all ambient monomorphisms with quotients
in the selected subcategory. [Thomason–Trobaugh, §3.1](https://gwern.net/doc/math/1990-thomason.pdf#page=66)
uses the degreewise split convention for its specified model and also
requires globally finite Tor-amplitude. This review does not silently
assert a model comparison with that convention. In particular, on a
non-quasi-compact scheme the present pointwise-local definition does not
supply a uniform global amplitude. TT §3.1.2 explains why its amplitude
condition is automatic for quasi-compact schemes; that observation does
not itself prove any of the excluded K-theory comparisons.

## Current-source verification

The focused command

```
lake --rehash build Quillen.PerfectComplexes.PerfectSupport Quillen.PerfectComplexes.Basic Quillen.Waldhausen.ChangeWeakEquivalences
```

passed with 2,968 jobs on the pinned toolchain/dependencies. New closure
and K-theory leaves were rebuilt from source. Only previously known linter
warnings were emitted. Evidence: `logs/perfect-k-theory-independent-build.log`.
This is a focused build, not a full repository or archive verification.

`audits/PerfectKTheoryIndependentAudit.lean` then passed all **412**
Waldhausen/PerfectComplexes-origin declarations, including private and
elaborator-generated helpers. It selects by defining module rather than
public-name prefix and recursively checks every declaration's axiom
closure. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
Per-declaration evidence and explicit endpoint checks are in
`logs/perfect-k-theory-independent-all-axioms.log`.

All thirty source fingerprints and the author audit match
`logs/perfect-k-theory-checked-sources.sha256` both before the build and after
the independent audit. That manifest's SHA-256 is
`ca3d22ba0318db751a9feea55bf26de516497929169a7606261f654cd30ed6d5`.
Independent audit-source fingerprint:
`logs/perfect-k-theory-independent-audit-source.sha256`.
Hash-check evidence:
`logs/perfect-k-theory-independent-initial-hash-check.log` and
`logs/perfect-k-theory-independent-final-hash-check.log`.

The source-token audit passed. No frozen proof source, public facade,
configuration, or script was changed by this review. Public integration
and clean archive verification remain coordinator-owned checks.

**Accepted: the actual locally-perfect and supported locally-perfect
Waldhausen connective K-group endpoints, within the exact scope above.**
