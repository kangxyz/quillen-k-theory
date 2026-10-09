# Independent review: strict compact HELP over the displayed base

## Status and frozen scope

**Accepted at the stated scope.** The complete semantic review, fresh
excluded-target seven-source rebuild, fixed-41 recursive-origin audit and all
21 strengthened consumers passed warning-free. The terminal audit completed
at 12:03:44Z on 2026-10-09, with all frozen and dependency hashes unchanged.

The source manifest is `logs/strict-over-base-sources.sha256`, SHA256
`6e1d8663341559e7b7174dcf21c76f448f0b2e012546a09fdb79a489ede100b5`.
The seven unchanged implementation hashes are:

| Source under `Quillen/Topology/` | SHA256 |
|---|---|
| `HomotopyLifting/VariableTime.lean` | `9e665dd3ab44877ed5343ef3a998e15d94007dcb933273f846b7fefb5eaafe4a` |
| `HomotopyLifting/Stationary.lean` | `271eb3135df1a58d8a469856f8bcbbc49b4c80e9ad29f7177722ea1969699199` |
| `HomotopyLifting/ParallelLifts.lean` | `eff6042aa710a30fd3e517883c0ad5e3c18de787078bf249f6c8014fb660b6ae` |
| `HomotopyLifting/OverBaseCorrection.lean` | `15bf34b2690c630a71c2a54a325731f3c741eaa4ef74f09832010966edfed41d` |
| `HomotopyLifting/CubeDuration.lean` | `85ddd62409b912b2564a01a469c26843f12632ade1f2d010e7d5f1dd19153bea` |
| `HELP/ContractibleTestOverBase.lean` | `a98954b71b8eeb55a8d328e252437be11488cc69e848fa9bf63f5bf57adb0bd6` |
| `HomotopyLifting/CubeOverBase.lean` | `449e6832ea414f71a5a1915f60c533ef1daaaa68967d4de8ead485ca9ec0c9e8` |

## Exact mathematical contract

For the original continuous maps `p:E→B`, `q:F→B`, and `f:E→F`, with the
literal equality `q ∘ f = p`, the hypotheses are genuine HLP for `p` and
`q` and full compact HELP of each original strict-fiber transition. These
are the repository's actual lifting predicates, not assumed equivalences.

The general test has compact source and target, actual HEP, a displayed
contraction of the target, and a continuous unit-interval duration whose
zero locus equals the entire image of its boundary map. For an original
strict square, `strictHELP_over_contracted_test` constructs an extension
`c` with the exact original boundary, exact base coordinate `p ∘ c=q ∘ b`,
and a genuine homotopy `f ∘ c ~ b` lying over that base at every time. Its
restriction to the whole boundary is literally the prescribed constant
track `f(a(x))`, for every time and boundary point.

The cube theorem supplies those test hypotheses from the actual lifted
finite cube and its entire original boundary. Its duration is the literal
product of `xᵢ(1−xᵢ)`. The product vanishes exactly on the full boundary;
in dimension zero it is one. The zero-dimensional endpoint has no added
positive-dimension or nonempty-source premise.

The HLP and HELP results use a common universe, matching the existing
universal HLP API. The compact-family continuity lemma has independently
varying object universes and imposes no separation condition on its target.

## Semantic proof review

1. **Acceleration at zero duration.** The generalized tube lemma gives a
   uniform neighborhood for an entire compact family constant at one
   parameter. This proves continuity even with an arbitrary, discontinuous
   selector of its compact coordinate. Applied at zero duration, it
   justifies the actual accelerated homotopy. Away from zero, ordinary
   continuous division suffices. Evaluating at `t·duration(x)` recovers the
   original homotopy at every time, including duration zero.
2. **Stationary lifting.** Genuine HLP lifts the accelerated homotopy;
   rescaling its actual time fixes every zero-duration parameter. No
   regularity of an arbitrary HLP choice is assumed. Both the exact original
   projected homotopy and the whole fixed zero set are retained.
3. **Parallel lifts and coherence.** The reverse-first/second concatenation
   projects to the explicit backtrack `|2t−1|`. Its actual contraction uses
   `1−(1−r)(1−|2t−1|)`. The correction duration
   `t(1−t)·duration(x)` fixes both path endpoints and every point in the
   original zero set. The exported two-parameter homotopy is the same
   constructed lift, with its exact projection and both levels of endpoint
   data; it is not an unrelated path-class witness.
4. **Two-stage correction.** The first lift restores the required source
   base coordinate. Comparing its image under the original `f` with the
   original comparison homotopy gives parallel lifts of the same original
   base homotopy. The second correction makes the endpoint comparison
   vertical. Both stages preserve the whole boundary zero set.
5. **Contracted and cubical tests.** The accepted ordinary contracted HELP
   supplies the initial comparison. Its full constant boundary is used in
   the correction, and the exact original boundary extension is recovered
   pointwise. The cube specialization uses the accepted actual boundary
   homeomorphism/HEP, rather than HEP of an arbitrary closed subset.

No conclusion is hidden in a hypothesis. No global continuous inverse
family is introduced.

## Independent Lean verification

Replay preparation: `logs/prepare-strict-over-base-independent.py`.
Replay checks: `logs/verify-strict-over-base-independent.sh build|audit`.
Overlay/evidence directory: `logs/strict-over-base-independent-20261009/`.
The overlay excludes every artifact for all seven targets before rebuilding;
its first `LEAN_PATH` entry contains freshly generated, nonsymlink target
oleans. Source dependency resolution and direct compiler dependency output
record the actual imported artifacts.

All seven source checks passed warning-free in the isolated overlay on
2026-10-09, from 12:01:39Z to 12:02:00Z. The checks use the shared slot1 lock
with logged acquisition, `lean -j1`, no broad Lake build, and unchanged
production sources/artifacts. Lean is 4.34.0. The manifest records 3,403
transitive dependency sources, 15,734 dependency artifacts, and the three
project/toolchain pins, checked before and after each phase.

The independent audit is `audits/StrictOverBaseIndependentAudit.lean`.
It imports the public `Quillen.Library` as a collision check, scans every
constant by defining module, and recursively checks axioms of all declarations,
including private/generated origins. The fixed expected count is 41:
11 VariableTime, 2 Stationary, 14 ParallelLifts, 1 OverBaseCorrection,
11 CubeDuration, 1 ContractibleTestOverBase, and 1 CubeOverBase.
The allowed axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.
The mutable public umbrella is not counted as one of the frozen target sources.

The fixed-41 audit passed without any consumer repairs. Its log is
`logs/strict-over-base-independent-20261009/audit.log`; acquisition and terminal
status are in `logs/strict-over-base-independent-audit-driver.log`. The final
evidence manifest is `logs/strict-over-base-independent-20261009/artifacts.sha256`.

The 21 consumers include independent-universe compact-family continuity,
exact scaled-time recovery, whole-zero-set lifting, the all-zero-duration
case, exact original correction maps, full two-parameter coherence with both
endpoint levels, duration/full-boundary range equality, empty-product degree
zero, general compact contracted tests, and literal pointwise cubical base
and boundary formulas. The original strict cube endpoint is checked explicitly
at dimension zero.

## Scope limits

This seven-source boundary proves strict-square HELP with a vertical
comparison constant on the whole boundary. The separate full-prescribed-track
extension/unpadding companions are excluded. No equivalence between ordinary
and vertical mapping-path endpoints, restriction of arbitrary stored paths
to a chart, finite-cover fiber gluing, or global weak-cartesian conclusion
is accepted by this review. Those require their own actual map constructions.
