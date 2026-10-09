# Independent review: genuine cylinder factorization on original quotient rows

Accepted 2026-10-09 10:45 UTC. The 295 source lines and original joint-row,
complex joint-cylinder, nested-row and mixed-chain prerequisites were inspected.
Both frozen sources were rebuilt in a fresh excluded-target overlay. All 72
recursive origins (57+15) and 30 consumers passed warning-free with unchanged
source/prerequisite hashes and only standard Lean logical axioms.

Boundary: `logs/row-cylinder-factorization-sources.sha256`.

## Actual row cofibrancy and exactness

The generic `JointData` contains structural data on the base category only:
an exact joint-arrow functor, its actual endpoint coproduct cocone, its actual
coarse-weak projection and the original factorization identity. It does not
assume any desired factorization, Reedy condition or equivalence on rows.

The source row and both endpoint injections are the original joint-row
construction evaluated pointwise. The displayed endpoint-sum square is an
actual pushout in the original full row category, proved from the genuine
component coproduct pushouts. Pushout stability of the already constructed
row Waldhausen structure makes the first endpoint a genuine Reedy cofibration.
Composition with the original joint-row cofibration proves the actual first
factor's row cofibrancy. This is not inferred from component cofibrancy alone.

The projection retains its original components and is coarse-weak pointwise.
The factorization equation holds on the unchanged original row arrow. The
middle functor is genuinely exact for fine row structures through accepted
joint-row exactness. Coarse exactness is separately derived from that original
projection and coarse two-out-of-three. Fine-square preservation needs no
fine saturation. Middle, inclusion and projection commute strictly with every
original ordinal reindexing.

## Genuine complex instance

The accepted identity-cone joint functor supplies all base data. The resulting
row inclusion is exactly the original identity-cone first factor at each
interval; the projection is exactly the original cone projection and is an
actual quasi-isomorphism. This instance states zero, repletion, extension,
finite-product, cone and positive-shift closure explicitly. The audited
bounded-term and arbitrary-scheme instances derive the required closure
properties; no kernel closure, global projectivity or scheme regularity is
needed for this structural factorization.

## Exact consumers and limits

The original 27 consumers expose actual Reedy cofibrations, endpoint coproduct
maps and isomorphisms, fine/coarse exactness, original components, strict
reindexing, degree zero, bounded terms and arbitrary schemes. Three additional
consumers combine this endpoint with the independently accepted mixed-chain
replacement and completion:

- A coarse-weak chain of actual quotient rows is replaced by genuine
  fine-cofibration/coarse-weak row arrows.
- The unchanged replacement preserves pointwise fine-weak transformations.
- The replaced chain lies in the essential image of the original relative-row
  initial-filtration functor, via actual cofiber completion.

The replacement projection remains coarse-weak. It is not a fine-category
natural equivalence and does not by itself prove a mixed-model or K-equivalence.
Global fibration and Gillet–Waldhausen remain separate obligations.

## Evidence

Script: `logs/verify-row-cylinder-independent.sh`.
First-path overlay: `/tmp/quillen-row-cylinder-independent-1039`.
Audit: `audits/RowCylinderFactorizationIndependentAudit.lean`.
Evidence: `logs/row-cylinder-independent-artifacts.sha256`.
The first strengthened consumer pass needed an explicit local instance exposing
the already derived coarse row two-out-of-three property under the nested
package. That audit-only repair and its initial log are preserved. No production
source was changed. The final fixed-72 audit and all 30 consumers passed.
This boundary is outside the delivered 09:45 version6 archive.
