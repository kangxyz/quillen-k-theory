# Exact compact boundary-track cover

Status: the generic source compiled warning-free at 2026-10-09 14:29:31 UTC
and is frozen in `logs/boundary-track-cover-sources.sha256`, manifest
fingerprint `7fa51e274d64480f4c1b15c409bf7f9716c51928d8ee020f2b41443c0a09e825`.
The ordered source replay, fixed 13-origin recursive audit, and all 14
consumers passed warning-free at 2026-10-09 14:32:26 UTC, with only
`propext`, `Classical.choice`, and `Quot.sound`. Source hashes match.
Independent review is underway; its acceptance is not yet claimed.

Let `A` be compact, `D` Hausdorff, `i : A → D` and `b : D → F` continuous,
and `H : I×A → F` the entire actual prescribed boundary track. Let `q : F → B`
be continuous, `N ⊂ F` and `V ⊂ B` open. The assumptions are exactly:

- `q(H(t,a)) = q(b(i(a)))` for every original time and boundary point;
- every point `y` with `q(y) ∉ V` lies in `N`.

The source defines the literal bad set as the image of `H⁻¹(Nᶜ)` under
`(t,a) ↦ i(a)`. Its closedness is derived from the compact closed subset of
`I×A` and the Hausdorff codomain `D`. It does not require injectivity or HEP
of `i`, compactness of `D`, or separation of `A`, `F`, or `B`.

The exact sets are `U0 = b⁻¹(N) \ bad` and `U1 = (q∘b)⁻¹(V)`. Both are
open and their union is all of `D`. The output retains the original formulas:

- `b(U0) ⊂ N`;
- if `i(a) ∈ U0`, every `H(t,a)` lies in `N`;
- if `i(a) ∈ U1`, every `H(t,a)` lies in `q⁻¹(V)`;
- every point outside `U1` lies in `U0`;
- every bad parameter lies in `U1`.

The whole-track statement comes from the exact bad-set construction and the
complement-fiber property. Endpoint containment is never substituted for it.
This source supplies cover data only: no arbitrary-closed-subset HEP, local
lifting, mixed attachment, or global gluing theorem is asserted.

Implementation: `Quillen/Topology/HELP/BoundaryTrackCover.lean`, namespace
`Quillen.BoundaryTrackCover`, with independent universes for all four spaces.

Author audit: `audits/BoundaryTrackCoverAudit.lean`; log
`logs/boundary-track-cover-initial-audit.log`. The consumers include distinct
object universes, empty boundary source, and the actual finite cube-boundary
inclusion in arbitrary dimension and explicitly in dimension zero.

Final guarded log: `logs/boundary-track-cover-fixed13.log`.
Author evidence: `logs/boundary-track-cover-evidence.sha256`.
