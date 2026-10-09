# Independent review: fiber HELP and actual realization lifting

## Accepted scope

Accepted after full semantic inspection, fresh isolated compilation of all
five sources, and the fixed-18 recursive-origin audit with 16 exact consumers.
All checks passed warning-free. The terminal audit completed at 10:15:52 UTC
on 2026-10-09, with source and inspected prerequisite hashes unchanged.

Manifest: `logs/fiberwise-realization-lifting-sources.sha256`, fingerprint
`cad6838995a966fc9bccf7bc7e91f0ee439e4b99da9849d532be200f476118da`.
All paths below are relative to `Quillen/Topology/HELP/`.

- `StrictPair.lean`:
  `a32ed75e4fa9143fc6fa1954eb1c8c7e9f6e2808578a0be413683af93eac97ea`
- `ContractibleTestFull.lean`:
  `65cda7c55d85b48aaee1af41a3af6d249835c2c442d672f97fd56b6dea18f794`
- `PairLifting.lean`:
  `be5171733acf375743aeff7af10bc799a0e735af740e8a3c04511fb496cc9d7d`
- `FiberwiseRealizationLifting.lean`:
  `338cefd91fb6165a0ecb47a6033aca340b9156352cad9b72f2dc9504e0946239`
- `FiberwiseRealizationEquivalence.lean`:
  `947ea640e220a95a2da8ac46c3460cbaaf6e450d278e89b9f362d311c32b9eb6`

No production source was modified during review.

## Full boundary preservation

`fullHELP_at_pair_of_strict` exposes the strict-to-full argument for a
single actual HEP pair. It requires strict lifting for all maps on that same
pair; compactness is not needed for this generic conversion. It extends
the reversed prescribed boundary homotopy, obtains a strict square for a
modified target map, applies strict lifting, and concatenates its relative
homotopy with the extended reverse homotopy. The whole boundary at this
stage is the prescribed homotopy with a constant prefix. The actual HEP
unpadding theorem removes that prefix while fixing the endpoint maps. The
result satisfies `K(t,i(x)) = H(t,x)` for every time and boundary point.

`fullHELP_on_contracted_test` applies this to the separately accepted actual
strict lifting theorem on compact contracted targets. Both original
projections have genuine HLP and every original strict-fiber map has compact
HELP. The latter premise is appropriate: the HEP reduction changes the
target map, and hence may change the required fiber point. No fixed-point
condition on the contraction is assumed. The test pair itself is unchanged.

`endpoint_hasLiftingProperty_of_pairHELP` constructs a literal lift into the
original mapping-path space. Its source coordinate is the HELP lift and its
path coordinate is the actual supplied homotopy. Full boundary equality
proves equality of the entire mapping-path lift on the boundary. Endpoint
agreement alone would be insufficient; the implementation uses the full
condition correctly.

## From simplex tests to all realized monomorphisms

`endpoint_realization_mono_of_fiberHELP` first solves each actual realized
simplex-boundary inclusion. The standard simplex is compact via the actual
realization homeomorphism. Its contraction comes from the actual nerve of
the finite ordinal and the genuine classifying-space contraction from an
initial/terminal object. The existing realized-boundary HEP theorem applies,
including the empty boundary in dimension zero.

The supporting `hasLiftingProperty_realization_mono` was read. It uses the
actual relative simplicial skeleton, actual realized coproduct cocones and
pushouts, and the genuine transfinite-composition lifting theorem. Thus the
conclusion is literal right lifting of the original mapping-path endpoint
against every realized simplicial monomorphism. The test realization need
not be compact. No continuous inverse family on arbitrary fibers is assumed
in this cellular construction.

## Genuine homotopy equivalence for realization totals

`homotopyEquivOfRealizationFiberHELP` additionally assumes that the two
original total spaces are actual simplicial realizations. Lifting against
the realized empty-subcomplex inclusion gives a section of the actual
mapping-path endpoint. Projection to its source gives an inverse candidate;
its stored paths give the right inverse homotopy. Lifting against the actual
simplicial cylinder endpoint monomorphism gives a homotopy between that
section composed with the original map and the actual mapping-path
inclusion. Projection supplies the left inverse homotopy. The supporting
cylinder endpoint monomorphism and its realization cylinder identification
were inspected. The forward map is definitionally the original `f`.

## Exact limits and assumptions

All spaces lie in the common arbitrary universe required by the existing
HLP and realization APIs. The original projections require genuine HLP;
all original strict-fiber maps require full compact HELP. These are
structural fiber hypotheses, not an assumption of the desired total-map
lifting or equivalence. There is no separation, local-compactness,
connectedness or nonemptiness premise on the original spaces.

The full-HELP theorem is restricted to compact contracted test targets.
The realized-mono lifting theorem is valid for arbitrary original total
spaces. The final homotopy equivalence requires both totals to be actual
simplicial realizations. No realization/CW model for an arbitrary homotopy
pullback is asserted, and no global compact HELP on all test spaces or weak
cartesian pushout/gluing theorem is claimed.

## Independent validation and evidence

The first-`LEAN_PATH` overlay is
`logs/fiberwise-realization-lifting-independent-20261009/olean`; all five
reviewed artifact stems are excluded before fresh compilation, while
unchanged prerequisites are symlinked. Source and inspected prerequisite
hashes are checked before and after each validation phase. Shared slot1 and
single-threaded Lean are used.

`audits/FiberwiseRealizationLiftingIndependentAudit.lean` recursively audits
all 18 origins in the five defining modules (1+1+1+1+14), permitting only `propext`, `Classical.choice` and
`Quot.sound`. Its 16 consumers also import `Quillen.Library` and the accepted
basepoint HELP transport. They test the complete prescribed boundary,
literal mapping-path lifting, all realized monomorphisms and explicit
zero-dimensional boundaries, the unchanged forward map and both actual
inverse homotopies, all finite homotopy sets including zero, empty totals,
component surjectivity, and the single chosen-fiber application using
individual joined base paths.

Script: `logs/verify-fiberwise-realization-lifting-independent.sh`.
Evidence directory: `logs/fiberwise-realization-lifting-independent-20261009/`.

Terminal logs: `check.log`, `audit.log`, `deps.log`,
`audit-hashes-after.log`, `audit-prerequisites-after.log` and the acquisition
record in that directory. The two validation commands exited successfully.
Artifact manifest: `logs/fiberwise-realization-lifting-independent-20261009/artifacts.sha256`.
