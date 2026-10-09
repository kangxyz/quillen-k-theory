# Original weak maps and weak-cartesian comparisons over coproducts

The two-source boundary is:

- `Quillen/Topology/HomotopyFiber/WeakCoproduct.lean`
- `Quillen/Topology/HomotopyPullback/WeakCoproduct.lean`

Both use the complete weak-equivalence property: actual surjectivity on path
components together with bijectivity on every finite based homotopy set.
Empty index types and empty summands are included.

## Exact endpoints

`Quillen.WeakCoproduct.fiberHomeomorph f i y` identifies the actual fiber of
`f i` over `y` with the actual fiber of the index-preserving sigma map over
`⟨i,y⟩`. Its source is literally `⟨i,x⟩`, and its whole path is literally
postcomposition with the original sigma inclusion. The proof uses the genuine
component pullback homeomorphism and the constant-parameter fiber homeomorphism.

`Quillen.WeakCoproduct.isWeakHomotopyEquivalence_sigma` derives the complete
weak property of the original sigma map from the component weak properties.
The proof uses the actual all-fiber criterion; no nonemptiness assumption is
added.

`Quillen.HomotopyPullback.comparison_sigma_factorization` is a definitional
identity of the original constant-path comparison with the sigma of component
comparisons followed by the actual pullback/coproduct homeomorphism.
`comparison_sigma_isWeakHomotopyEquivalence` therefore assembles original
weak-cartesian squares with a common target.

The universe scope is one arbitrary common universe for index, total and base
spaces. No compactness, separation or local contractibility premise is needed.

## Validation

The source manifest is `logs/weak-coproduct-sources.sha256`.
`audits/WeakCoproductAssemblyAudit.lean` recursively checks exactly six
module-origin declarations and permits only `propext`, `Classical.choice` and
`Quot.sound`. Its thirteen consumers include exact whole-path formulas,
component surjectivity, empty index and empty component cases, and explicit
dimension-zero maps. The initial source/audit check passed warning-free;
the fixed-count rerun is recorded in `logs/weak-coproduct-fixed6-pasting-check.log`.

This is coproduct closure. Finite pushout gluing and the global connected-row
realization fiber theorem remain separate obligations.
