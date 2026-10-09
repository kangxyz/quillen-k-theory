# Original relative filtrations and weak-map detection

## Actual object predicate

`RelativeRows.WeakChains` uses the unchanged initial filtration
`i ↦ A[0,i+1]`. Each filtration arrow is an actual fine cofibration. Under
the structural `ExtensionAxiom N.coarse`, the actual relative-row condition
is equivalent to coarse weakness of every original filtration arrow.

The proof uses each original displayed quotient square. Only its genuine
zero corner is transported to the chosen coarse zero; the original
cofibration, quotient object and quotient map stay unchanged. The accepted
weak-cofibration/acyclic-cofiber characterization then applies. No saturation
or cylinder hypothesis is used for this predicate theorem.

## Original functor and fine maps

`RelativeRows.FiltrationWeakMaps` defines
`initialFiltrationFunctor N n : Obj N n ⥤ ComposableArrows C n.len`.
Its maps are literal whiskerings of the original natural transformations,
and its first vertex is the original `first N n` object. It is strictly
compatible with every original ordinal restriction.

`weq_iff_initialFiltrationFunctor` detects actual fine row weak equivalences
from the original filtration components. The reverse direction is genuine
Waldhausen gluing on every original quotient square. Diagonal components
are actual isomorphisms between zero objects. This theorem needs neither
fine nor coarse extension/saturation and introduces no exactness witness
as a conclusion-shaped hypothesis.

All statements allow independent object and hom universes. The functor
lands in the exact finite-diagram type consumed by
`FunctorialFactorization.finiteReplacement`; no categorical model adapter
is hidden in that interface.

## Boundary

These results do not establish fullness, essential surjectivity, a quotient
presentation equivalence, cylinder comparison equivalence, or the global
relative-realization fiber theorem. Those remain distinct obligations.

## Verification

Both sources compile warning-free. Frozen source manifest:
`logs/relative-rows-weak-chains-sources.sha256`.
Own audit: `audits/RelativeRowsWeakChainsAudit.lean`, covering every origin
recursively plus original-map, independent-universe and degree-zero consumers.
Initial and terminal fixed22 audits both passed warning-free, covering
12 WeakChains origins and10 FiltrationWeakMaps origins. All13 original-map,
independent-universe and degree-zero consumers passed. The final audit log is
`logs/relative-rows-weak-chains-audit-final.log`; the exact source hashes were
rechecked. `logs/relative-rows-weak-chains-artifacts.sha256` records all source,
audit, terminal-log and report evidence. Independent review is separate.
