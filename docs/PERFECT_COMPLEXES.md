# Perfect-complex K-theory: checked construction and remaining comparisons

This development is separate from the public `Quillen.Scheme.K` API, which
uses vector bundles and Quillen's Q-construction. `PerfectK` is now a genuine
connective Waldhausen construction on actual locally perfect sheaf complexes.
The comparison maps below are constructed; comparison equivalences and
localization theorems are not thereby proved.

## Checked construction

The ten `Quillen.Waldhausen` modules provide:

- The conventional zero/cofibration/weak-equivalence/gluing axioms, with no
  K-theory conclusion stored as an input.
- Actual diagonal S-simplices `[n] × Ar[n] → C`, with zero diagonals,
  cofibration rows, quotient pushout squares, and pointwise weak equivalences.
- The actual geometric realization, zero vertex, and groups `π_(n+1)`.
- Exact-functor simplicial, continuous, and group maps. Rebasing by the
  canonical zero-object isomorphism handles preservation of zero up to iso.
- Exact-category and abelian-complex instances. For complexes, weak
  equivalences are quasi-isomorphisms and gluing is proved by the homology
  five lemma applied to the pushout exact sequence.
- Inherited Waldhausen structures on replete extension-closed full
  subcategories containing zero, and actual inclusion maps between them.

The `Quillen.PerfectComplexes` modules provide:

- `Strict`: globally termwise bounded complexes of finite locally free sheaves;
  their repleteness, zero and extension closure; genuine `StrictK`.
- `VectorBundleInclusion`: exact degree-zero inclusion and its S-K comparison.
  All ambient exact sequences are preserved, including locally split ones.
- `Restriction`: actual geometric strict restriction and its K-map.
- `Local` and `LocalRestriction`: genuinely local perfectness through actual
  quasi-isomorphism localization, derived-isomorphism invariance, open
  restriction, and strict-to-local inclusion.
- `LocalLifting`, `LocalHomotopyStep`, `LocalNullHomotopy`, and
  `LocalQuasiIsoLifting`: actual local lifts through epis, finite shrinking
  construction of nullhomotopies, and lifting through quasi-isomorphisms.
- `DerivedMorphisms` and `DerivedRepresentativeNaturality`: actual local
  chain representatives for derived morphisms with strict-perfect source,
  compatible with every derived restriction lift.
- `Closure`: actual strict-perfect shift and mapping-cone closure.
- `DerivedStructure`, `LocalModels`, `LocalTriangles`, and `Extension`:
  constructed triangulated derived restriction, common local models,
  mapping-cone comparison, and proved local-perfect extension closure.
- `KTheory`: the genuine `perfectWaldhausen`, `PerfectK`,
  `strictToPerfectKMap`, `vectorBundleToPerfectSMap`, and `perfectKRestrict`.
- `Support` and `PerfectSupport`: actual acyclicity on an open, supported
  strict/local-perfect Waldhausen K-groups, canonical inclusion/comparison
  maps, and the actual restricted quasi-isomorphisms to zero.

The geometric extension proof uses finite local lifting, not global
projectivity of vector bundles or an assumed global strict representative.
Its architecture is described in
[PERFECT_COMPLEXES_LOCAL_ROADMAP.md](PERFECT_COMPLEXES_LOCAL_ROADMAP.md).

## Comparison and remaining scope

1. Quillen Q/S comparison is now separately proved for arbitrary exact
   categories. `QuillenComparison` uses it and the actual small-model bridge
   to construct maps from public `Scheme.K` to strict/local-perfect K.
   It does not yet prove those degree-zero inclusion maps are equivalences.
2. Gillet–Waldhausen equivalence for bounded complexes.
3. Strict-perfect versus locally-perfect equivalence under geometric
   resolution/ample-family hypotheses.
4. A homotopy-fiber/localization sequence for supported perfect K-theory.
5. A nonconnective spectrum or Thomason–Trobaugh localization.
6. K₀ commutativity from Waldhausen additivity. Positive K-degrees already
   inherit commutativity from their actual higher homotopy groups.

None of these conclusions is inserted as a structure field or proof
placeholder. The construction is connective. On arbitrary non-quasi-compact
schemes, its explicitly local object condition must not silently be identified
with a convention additionally imposing uniform global Tor-amplitude.

## Primary reference and mathematical scope

[Thomason–Trobaugh, *Higher Algebraic K-Theory of Schemes and of Derived
Categories*](https://gwern.net/doc/math/1990-thomason.pdf): §§1.2 and 1.5
supply the Waldhausen/S model. Theorem 1.11.7 assumes the exact embedding is
fully faithful and extension-closed, reflects exact sequences, and makes
ambient epimorphisms admissible (§1.11.3). §§3.8–3.10 compare strict and
all-perfect K-theory under an ample family of line bundles. Theorem 7.4 is
nonconnective localization for quasi-compact quasi-separated schemes and
quasi-compact open immersions. TT §3.1 additionally imposes globally finite
Tor-amplitude; §3.1.2 makes it automatic for quasi-compact schemes. These
comparison/localization results remain the roadmap, not imported assumptions.

## Verification and review

All named modules above passed focused builds or serial direct `lean -j 2`
checks. `audits/PerfectKTheoryAudit.lean` imports the full locally-perfect and
support endpoints and audits every declaration originating in the Waldhausen
and PerfectComplexes modules, including private/generated helpers. See
`logs/perfect-k-theory-all-axioms.log` for the current result.

The earlier 17-module foundational subset received an independent rehash
build, semantic review, and 270-declaration axiom audit:
[foundations review](REVIEW_20261009_PERFECT_FOUNDATIONS.md). That historical
review does not automatically cover the subsequent local closure/K endpoint.
The larger checkpoint is frozen separately for independent review.

No existing `Scheme.K` definition or previously migrated proof body is changed
by these modules. A focused build is not a claim that all concurrent repository
changes have passed the full archive audit.
