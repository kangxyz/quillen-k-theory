# Independent acceptance: finite adjacent-coordinate algebra

Accepted after full semantic inspection, a fresh isolated source build, a
fixed41 recursive-origin audit, thirteen exact consumers, and unchanged source
hashes. All final checks passed warning-free.

## Exact scope

For an arbitrary actual `CommGroup G`, the original incidence homomorphism is
literally

```lean
x ↦ Fin.cons 1 x * Fin.snoc x 1
```

on `Fin n → G`, with target `Fin (n+1) → G`. Multiplication is the existing
pointwise group multiplication. The first and last term contributions and the
full recursive incidence formula are proved for these exact maps.

The original Euler homomorphism recursively takes the head divided by the
Euler product of the tail, starting with the unit on the empty tuple. Thus its
signs alternate from the first coordinate. The recurrence proves that Euler
annihilates each original incidence tuple. Incidence is injective: equality
first identifies the initial disk coordinate, and cancellation reduces the
remaining coordinates to the induction hypothesis.

Conversely, a unit Euler product is solved constructively for an original
incidence preimage. The proof removes the first disk contribution from the
tail, applies the induction hypothesis, and reinstates that first disk. The
length-zero disk case is checked explicitly. Consequently the actual Euler
kernel is exactly the original incidence image. The explicit initial-coordinate
inclusion is a genuine section of Euler and proves surjectivity.

There is no K-theory, fibration, acyclicity, category equivalence, or exactness
conclusion supplied as an input. The only mathematical structure assumed is
the actual commutative group. No new group law is introduced.

## Verification

Reviewed source: `Quillen/Algebra/FiniteAdjacentComplex.lean`.
SHA-256:
`615b15d63a955b14fac17024e96bac7cb319455854083262758ca826ada9f645`.
Independent manifest: `logs/finite-adjacent-core-independent-20261009/sources.sha256`.
Manifest SHA-256:
`d0c6c78a6b0494c5bcd47f0859783f470ad7386d54e9cbafd3e06fb347547a03`.

`audits/FiniteAdjacentCoreIndependentAudit.lean` enumerates all 41 exact
module-origin declarations, including generated/private declarations, and
recursively permits only `propext`, `Classical.choice`, and `Quot.sound`.
All thirteen consumers passed, including the literal incidence formula,
Euler annihilation, incidence injectivity, actual kernel/image equality,
unique incidence preimages, the original section, and explicit empty-disk,
one-term and two-term cases.

Evidence: `logs/finite-adjacent-core-independent-20261009/`.
`check.log` is the warning-free fresh build; `audit-final.log` is the fixed41
successful audit and consumer run. `deps.log` records fresh import resolution;
`hashes-before.log` and `hashes-after.log` match. `artifacts.sha256` freezes the
report, audit, scripts, logs and fresh artifact. The first-LEAN_PATH overlay
contains a freshly built selected olean, with unchanged dependencies linked.
The shared slot1 acquisition is logged. Production source/artifacts were not
modified by this independent review.

The separately authored arbitrary-coordinate section is a subsequent module
and is outside this independent acceptance.
