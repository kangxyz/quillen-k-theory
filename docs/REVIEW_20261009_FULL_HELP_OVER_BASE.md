# Independent review: full prescribed-boundary HELP over a fixed base

## Status and frozen sources

**Accepted at the stated scope.** Full semantic review, the isolated fresh
three-source rebuild, fixed-seven recursive-origin audit and all nine
strengthened consumers passed warning-free. The terminal independent audit
completed at 12:14:42Z on 2026-10-09, with all source/dependency hashes unchanged.

Manifest: `logs/full-over-base-sources.sha256`, SHA256
`150474fe58a1d391a37fd0402b56ae931a817ecd1863cf0da93431e6345e0003`.

| Source under `Quillen/Topology/` | SHA256 |
|---|---|
| `HomotopyLifting/FiberwiseExtension.lean` | `405f092fdfde67a9e3bc922d0056281e04a301c5a0aad484ec3c536acdc316da` |
| `HomotopyLifting/FiberwiseBoundaryCorrection.lean` | `210922997ecc749244c148c521ed8b6583d21dd15327811af9be3e56e211a159` |
| `HELP/ContractibleTestFullOverBase.lean` | `6ae502be869af26986e4e88f5e622f3cd2589d3c28ab718aa20d6e0f0209c91c` |

All implementation sources were preserved unchanged.

## Exact accepted contract

The original `p:E→B` and `q:F→B` have genuine HLP, and the original `f:E→F`
satisfies the literal equality `q ∘ f=p`. The original strict-fiber maps
have full compact HELP. The test has compact source and target, actual HEP,
a displayed contraction of the target, and a continuous duration vanishing
exactly on the image of the boundary map.

For the original boundary map `a`, target map `b`, and supplied homotopy
`H:f ∘ a ~ b ∘ i`, the extra condition says exactly that the entire supplied
`H` lies over `q ∘ b ∘ i`. It does not assert an extension or lifting result.
`fullHELP_over_contracted_test` constructs the actual `c` with `c ∘ i=a`
and `p ∘ c=q ∘ b`, together with a homotopy `V:f ∘ c ~ b` over that same
base. For every time and every boundary point,
`V(t,i(x))=H(t,x)` literally. The final boundary track is not merely constant,
endpoint-equivalent, or a reparameterization of the supplied one.

The topology and HLP APIs use a common universe. There are no separation,
positive-dimension, or nonempty-source assumptions. The independent consumers
also instantiate the actual finite cube and its entire boundary, explicitly
including the empty zero-dimensional boundary.

## Full semantic proof review

1. **Fiberwise extension.** Ordinary HEP first extends the supplied track.
   Treating `(t,x)` as the HLP parameter, its projected time coordinate is
   reversed along `(1−s)t`. The duration `t·d(x)` is zero both at the initial
   time and on the whole boundary. The stationary-lifting theorem therefore
   retains the original initial map and every original boundary value,
   including a nonconstant boundary track. At the terminal correction time,
   the projection is exactly the original fixed base map.
2. **Boundary correction.** Actual interval-square HEP extends the supplied
   boundary homotopy between tracks while preserving both endpoint maps.
   A second correction reverses the square-extension parameter. Its duration
   `s·t·(1−t)·d(x)` fixes the initial square, both path endpoints, and the
   entire boundary. Each of these four zero-locus cases is checked explicitly.
   The terminal corrected track retains the original endpoint maps and has
   exactly the desired projection and boundary track.
3. **Vertical unpadding.** The actual `delayReflLeft` homotopy removes the
   constant prefix from the boundary track. Its two endpoint values stay
   fixed and its projection remains the displayed base at every stage.
   The preceding square-correction theorem applies to this constructed
   two-parameter homotopy; such a comparison is not assumed in the final
   full-HELP theorem.
4. **Assembly.** Extend the reverse of the original `H` fiberwise from `b`.
   Its terminal map makes the initial boundary square strict. Apply the
   accepted strict over-base HELP theorem, then concatenate its comparison
   with the reverse extension. On the boundary this is the literal constant
   prefix followed by `H`. Vertical unpadding restores `H` exactly without
   changing either endpoint or the base coordinate.

Every correction uses actual HEP/HLP. No full conclusion is hidden in a
hypothesis, and no continuous family of inverse equivalences is chosen.

## Independent verification

Preparation: `logs/prepare-full-over-base-independent.py`.
Replay: `logs/verify-full-over-base-independent.sh build|audit`.
Evidence directory: `logs/full-over-base-independent-20261009/`.
Audit: `audits/FullOverBaseIndependentAudit.lean`.
Additional consumer source: `audits/FullOverBaseIndependentConsumers.lean`.

The overlay excludes all three target artifacts before its fresh ordered
rebuild and occupies the first `LEAN_PATH` entry. Its target oleans are new
regular files, not symlinks. The three source checks passed warning-free
between 12:08:49Z and 12:09:02Z on 2026-10-09. Source/compiler dependency
records verify the actual first-path imports. All Lean checks run at `-j1`
under the shared slot1 lock, with acquisition logs and no broad Lake build.

The dependency manifests cover 3,406 transitive source files, 15,737 compiled
dependency artifacts, and the three project/toolchain pins. They and the
frozen source hashes are checked before and after each phase. Lean is 4.34.0.

The independent audit imports `Quillen.Library` to catch declaration-name
collisions. It checks all defining-module origins, including generated
proof auxiliaries, recursively against only `propext`, `Classical.choice`
and `Quot.sound`. The fixed count is seven: one FiberwiseExtension origin,
five FiberwiseBoundaryCorrection origins, and one ContractibleTestFullOverBase
origin. The public umbrella is not part of the immutable target manifest.

The final audit log is `logs/full-over-base-independent-20261009/audit.log`;
its terminal/acquisition record is `logs/full-over-base-independent-audit-driver.log`.
An initial independent consumer attempt passed all seven origin checks but
needed an audit-only tactic goal-order repair in the zero-dimensional test.
The terminal fixed-seven rerun passed all consumers without warnings; no
implementation change was needed. The first attempt is retained in the evidence.
The final evidence manifest is `logs/full-over-base-independent-20261009/artifacts.sha256`.

Nine consumers check all four named theorems, literal endpoint/base/boundary
formulas, and the actual finite-cube specialization. A separate dimension-zero
consumer derives boundary verticality from the genuinely empty boundary,
without imposing it as an additional premise. A stronger mapping-path
consumer constructs a continuous map into the original compact-open
`MappingPath f`: its endpoint is exactly `b`, source restriction exactly `a`,
base coordinate exact, all stored paths vertical, and every stored boundary
path literally equals the supplied original `H` at every time.

## Limits

This is full prescribed-boundary HELP on the stated contracted compact tests.
It does not assert full HELP for arbitrary compact targets, a global
fiberwise inverse, or arbitrary closed-subset HEP. The vertical/ordinary
mapping-path comparison, chart-restriction identifications and global weak
fiber/gluing conclusion are separate source boundaries.
