# Independent acceptance: classification diagonal

Reviewed 2026-10-09 independently of the author of Classification.lean and
ClassificationHomotopy.lean. The two-source and author-audit fingerprints
are retained in `logs/classification-independent-sources.sha256`.

The rectangular simplicial model has invertible vertical arrows. Diagonal
evaluation to the actual ordinary nerve has a strict constant-vertical
section. The source constructs coherent transport through the initial row
and proves that it agrees with original ordered vertical arrows. Its
reindexing formula handles arbitrary faces/degeneracies, even those not
preserving the initial vertex or identifying different vertices.

Conjugating each grid arrow by this transport defines a valid diagram
for arbitrary row selections; monotonicity of the selected rows is not
silently assumed. The interval chooses the old row or the diagonal row,
giving an actual natural simplicial cylinder. Its endpoints are exactly
identity and evaluation followed by the constant section. The deformation
fixes every already constant diagram, hence the whole constant-nerve image
and every chosen vertex there.

Realization gives the actual homotopy equivalence with exactly diagonal
evaluation as forward map. Its two inverse identities and the fixed-vertex
formula are proved from this explicit cylinder. No rowwise realization
invariance theorem or unspecified inverse hypothesis is used. No semantic
blocker was found in this precise scope.

A separate current-source rehash build of ClassificationHomotopy passed.
The recursive declaration-origin audit was independently rerun and passed
all **81 declarations**: 47 in Classification and 34 in ClassificationHomotopy.
Only `propext`, `Classical.choice`, and `Quot.sound` occur in their transitive
axiom closures. Endpoint and fixed-vertex consumer examples also compile.
Both commands exited with code 0, and all source/audit hashes still match.

Evidence: `logs/classification-parent-build.log`,
`logs/classification-parent-all-axioms.log`, and
`logs/classification-parent-final-hash-check.log`. The review changed no
proof source. This later endpoint is outside the frozen 04:11 archive.
