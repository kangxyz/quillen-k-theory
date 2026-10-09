# All-degree basepoint-path transport

Author-owned implementation: `Quillen/Topology/HomotopyGroups/PathTransport.lean`.

## Exact contract

For arbitrary topological spaces `X : Type u`, `Y : Type v`, independently
sized, a genuine path `γ : Path x₀ x₁` defines

```lean
pathTransport γ n :
  HomotopyGroup (Fin n) X x₀ ≃ HomotopyGroup (Fin n) X x₁
```

for every natural number `n`, including zero. These are mathlib's original
boundary-relative cubical homotopy classes. There is no new homotopy-set model
or group structure.

For the actual continuous map `f : C(X,Y)`, the exact naturality formula is

```lean
pathTransport (γ.map f.continuous) n (homotopyGroupMap f rfl a) =
  homotopyGroupMap f rfl (pathTransport γ n a)
```

Consequently, each of injectivity, surjectivity, and bijectivity of the
original `homotopyGroupMap` is equivalent at the two endpoints. The APIs are
`homotopyGroupMap_injective_iff_of_path`,
`homotopyGroupMap_surjective_iff_of_path`, and
`homotopyGroupMap_bijective_iff_of_path`, with arguments `f γ n`.
`homotopyGroupMap_path_conjugate` exposes the entire function equality.

The `Joined` version uses an actual chosen path from that proposition. The
`PathConnectedSpace X` corollary propagates bijectivity from one source point
to every source point, separately for each degree. Thus path-connectedness
must be established for the actual space to which this corollary is applied.

## Construction and mathematical checks

The auxiliary space is the actual compact-open free path space
`C(unitInterval, X)`. Its evaluation map at any `t` is a genuine homotopy
equivalence. The inverse is the original continuous constant-path map.
The inverse homotopy sends `(s,p)` to the path

```text
r ↦ p((1-s)t + sr).
```

This begins at the constant path at `p(t)` and ends at `p`; evaluation after
constant paths is literally the identity. Continuity follows from the actual
compact-open evaluation map, interval local compactness, and continuous
convex combination. No local compactness, separation, compactness,
well-pointedness, or path-connectedness of `X` is required.

The previously proved all-degree theorem
`homotopyGroupMap_bijective_of_homotopyEquiv` applies to these displayed
homotopy equivalences at the source basepoint `γ.toContinuousMap`.
`pathStartEquiv` and `pathEndEquiv` have forward maps definitionally the
original endpoint-evaluation homotopy maps. Transport is the inverse of the
first followed by the second. No endpoint bijection is a hypothesis.

Actual postcomposition of free paths commutes strictly with both evaluations.
These squares descend to the original homotopy quotients, and cancellation
of the initial evaluation equivalence proves naturality. Conjugation then
proves the injectivity/surjectivity/bijectivity results.

Transport sends the original constant class to the original constant class,
and transport along `Path.refl` is the actual identity equivalence. Degree
zero uses no group operation and is explicitly checked in the consumers.
The construction avoids attaching an interval whisker or imposing a
closed-basepoint hypothesis.

## Scope

This module supplies all-degree set equivalences, pointed constant-class
preservation, exact naturality, and basepoint detection along actual source
paths. It does not claim a fibration or weak-Cartesian theorem. In particular,
path-connectedness of an unrelated base space does not by itself establish
the source-path hypothesis here. Group-valued packaging and concatenation or
path-homotopy coherence laws are not needed by this boundary and are not
additional exported claims.

## Source and checking boundary

Source SHA-256:
`0aa1157296407af9f2b4aa5a69ac28f2bfc8e678a6842c23f00a82c1788df3f0`.
Manifest: `logs/path-transport-20261009/sources.sha256`.
Manifest SHA-256:
`c53754a63c84cea3f26bd3a7c384676fb53947afeee4a1841366bf9aeee3a21c`.

The final focused source check is `logs/path-transport-20261009/check5.log`;
it passed warning-free. The check records actual acquisition of slot1.
The audit source is `audits/PathTransportAudit.lean`, with nineteen consumers
covering independent universes, original evaluation/constant-section/path
postcomposition maps, the exact transport construction and naturality,
all three detection properties, `Joined` and path-connectedness, and explicit
zero-degree naturality, bijectivity, constant-class and reflexive formulas.
The final fixed-count recursive audit passed all **28** defining-module origins,
including private/generated declarations, with only `propext`, `Classical.choice`,
and `Quot.sound`. All nineteen consumers passed warning-free. Evidence is
`logs/path-transport-20261009/audit-final.log`; source hashes were rechecked both
before and after that audit. Exact artifact hashes are in
`logs/path-transport-20261009/artifacts.sha256`.

This is the author's verification; independent review is separate. The new
source is outside the previously frozen 08:05 archive boundary.
