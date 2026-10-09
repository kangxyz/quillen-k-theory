# Independent review: actual acyclic cofibration sequences and disk layers

Accepted on 2026-10-09 after full semantic inspection, independent fresh
rebuild of all four new sources, fixed-count recursive audit, exact-forward-map
consumer checks, and source hash rechecks.

## Actual relative cofibrations

`ExactFunctorSequence.lean` derives admissibility of the genuine relative
pushout comparison from admissibility on actual quotient objects. It uses the
actual same-kernel pullback and the previously proved admissible pullback
lemma. Consequently, a pointwise conflation sequence of genuine exact functors
satisfies the full structural `IsCofibrationSequence` contract. The quotient
functor's exactness is an input, but the relative-cofibration conclusion is
proved and no additivity conclusion is an input.

`TruncationCofibrationSequence.lean` applies this to the original truncation
inclusion, identity functor, and actual cokernel projection. It proves the
contract both for isomorphism weak equivalences and actual quasi-isomorphisms.
The latter are all actual maps in the bounded acyclic category, by exactness
of their source and target complexes. No weak-equivalence predicate is
redefined to make that statement true.

## Actual disks and one-step quotient

`IdentityDisk.lean` uses mathlib's actual two-term double complex with identity
differential. Acyclicity, bounded termwise membership, naturality, and
preservation of short exact sequences are proved. The disk exact functor
requires repleteness, zero, and extension closure of the termwise subcategory;
it does not require kernel closure.

`TruncationLayer.lean` constructs the precise layer
`Q_n(truncLE_(n+1) K)`, whose inner truncation is the actual existing truncation
of `truncLE_(n+1) K`. It proves a natural isomorphism with the identity disk on
the original cycles in degree n+1. Both degree components, the invertible
differential, the original quotient maps, and naturality are derived. The
layer functor and the cycle-disk functor are separately constructed genuine
exact functors. Their forward-functor identities are definitional.

This does not yet identify the nested truncation with the original truncation
of K, prove telescoping on arbitrary bounded strata, prove additivity, or
prove Gillet–Waldhausen. Those are separate obligations.

## Evidence

The four new sources compiled warning-free in the isolated overlay. Together
with the previously accepted eight GW sources, the count-fixed recursive
audit passed all 275 GW declaration origins. The same audit also checked all
167 origins of the independently reviewed eleven-source additivity algebra.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. Arbitrary-universe
consumers checked the actual natural transformations, quasi-isomorphism
contract, disk/layer isomorphism, and exact-functor formulas. All frozen source
hashes match before and after.

- `audits/AdditivityGilletWaldhausenIndependentAudit.lean`
- `logs/additivity-gw-independent-sources.sha256`
- `logs/additivity-gw-independent-check.log`
- `logs/additivity-gw-independent-audit.log`
- `logs/additivity-gw-independent-hashes.log`

Combined fifteen-source manifest SHA256:
`8d913a4d95605db2151908ada4007e201fa8e770ddffec8efe0ab59b9ff5753b`.
This reviewed leaf work is outside the delivered 05:00 archive.
