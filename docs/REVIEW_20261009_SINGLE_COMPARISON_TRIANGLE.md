# Independent review: original single/change-of-weak comparison triangle

Accepted sources are the exact two in
`logs/single-comparison-independent/sources.sha256`:
`Waldhausen/GilletWaldhausen/SingleQuasiComparison.lean` and
`PerfectComplexes/SingleComparison.lean`, beneath `Quillen`.

Both sources and their original functor/K-map interfaces were read independently.
The coarse exact functor is precisely the same actual single-complex functor.
Its weak-map proof sends genuine isomorphisms to genuine quasi-isomorphisms.
Zero, cofibration and pushout preservation are the existing fine exactness
proofs. The normalized K-map triangle uses the actual identity change-of-weak
functor, the right unitor, original K-map composition, and normalization-invariant
natural-isomorphism comparison. No strict chosen-zero equality is presumed.

For arbitrary schemes, the original strict-perfect predicate is definitionally
the bounded-term finite-locally-free predicate. The original degree-zero single
functors agree on objects and maps; the public S-comparison therefore retains
exactly the same normalized K-map. The public Scheme.K consumer retains its
actual small-model Q/S conversion before the original fine single and
change-of-weak maps. No kernel closure, fibration, or Gillet–Waldhausen
equivalence is an input to either production theorem.

Independent validation passed warning-free: fresh isolated two-source rebuild,
fixed8 recursive origin audit, all eleven original exact-map/universe consumers,
and two additional explicit public K₀ consumers, one as a homomorphism into
strict-perfect K and one pointwise through the original strict/local map.
Every recursive dependency uses only the standard three axioms. Source hashes
match afterward, and no production source was changed.

Audit: `audits/GilletWaldhausenSingleComparisonIndependentAudit.lean`.
Log: `logs/single-comparison-independent/check.log`.
No semantic issue found. This is an original-map identification, not an
equivalence of the coarse single functor.
