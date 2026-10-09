# Independent acceptance: actual relative quotient rows

Accepted 2026-10-09 08:31 UTC. All five complete sources were inspected and
freshly built in an isolated first-LEAN_PATH overlay. The fixed76 recursive
origin audit and all27 original-map/class/ordinal consumers passed warning-free,
with exact source hashes matching before and after. Only propext,
Classical.choice and Quot.sound are permitted, including generated helpers.

The input is exactly NestedWeakEquivalences: genuine fine/coarse Waldhausen
structures with the same cofibrations and chosen zero, and actual inclusion of
the weak classes. No saturation, extension axiom, cylinder, fiber conclusion or
realization-equivalence conclusion is supplied.

The category is the actual full subcategory of one-longer quotient rows whose
tail objects are coarse-acyclic. All original natural transformations remain;
weak equivalences are the inherited fine class. Actual ambient row pushouts
and coarse gluing prove closure. Inherited cofibrations, the actual zero and
all Waldhausen axioms are derived.

Ordinal maps really fix the added initial vertex and send each successor
vertex to the successor of its original image. Their identities, composition,
zero compatibility and exactness are checked. The tail functor lands in the
actual fine acyclic row category. Its quotient squares and cofibration tests
are proved by original inclusion/reflection and actual relative pushouts.
The tail is strictly outer-natural; first-object evaluation is only degreewise.
No nonexistent outer naturality of the first object is claimed.

The original first/tail product functor is genuinely exact and its two literal
projections are retained. This structural boundary is separate from relative
additivity, the zero-tail split realization theorem and the global fibration.
Independent object/hom universes remain explicit.

Evidence: `logs/relative-rows-sources.sha256`,
`logs/relative-rows-independent-{prehash,build,audit,posthash}.log`,
`audits/RelativeRowsIndependentAudit.lean`. Fresh artifacts are in
`/tmp/quillen-post0805-independent-0828`. Fixed counts are
2 + 18 + 28 + 11 + 17 = 76. This boundary is post08:05.
