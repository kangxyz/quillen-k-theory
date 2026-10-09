# Independent review: original weak equivalence from finite boundary lifting

## Scope and semantic result

The reviewed frozen source is
`Quillen/Topology/CubicalSubdivision/BoundaryWeakEquivalence.lean`, SHA-256
`d37154ca1376590c4b8bfc7eaf7e611da3a5459ce88107c3139dda076a4a9930`.
The author's manifest is `logs/boundary-weak-equivalence-sources.sha256`.
No production source was changed during this review.

The full source and its actual boundary-homeomorphism/cylinder dependencies
were read. No semantic defect was found. Literal finite cube-boundary RLP
implies complete weakness of the original continuous map, retaining independent
source and target universes. The proof does not assert arbitrary compact HELP.

The zero-cube has an actually empty boundary, so its strict lift gives point
surjectivity, including the empty-source case. Surjectivity in every finite
homotopy degree lifts the original generalized loop with its prescribed
constant boundary. Injectivity uses the actual cylinder-boundary pushout,
whose source is definitionally the next canonical boundary presentation.
The accepted first-coordinate homeomorphism identifies its map with the
next cube-boundary map. The strict filler is therefore an actual homotopy
between the original representatives, fixed on the whole original boundary.
The resulting quotient map is precisely the existing `homotopyGroupMap`.

## Independent validation

The root module output directory was copied into an isolated overlay. All
cached target artifacts were renamed out of the importable target paths.
The source was rebuilt directly with that overlay first in `LEAN_PATH`.
The fixed-six recursive origin audit and thirteen original-map consumers are
`audits/CubicalBoundaryWeakIndependentAudit.lean`. The fresh source rebuild,
fixed-six recursive origin audit and all thirteen consumers passed warning-free
with terminal status zero at 2026-10-09 11:45:13 UTC. Only `propext`,
`Classical.choice`, and `Quot.sound` occur recursively. All recorded hashes
matched before and after validation.

Consumers include strict point surjectivity, empty-target consequence,
component coverage, arbitrary finite degrees and explicit degree zero,
independent source/target/parameter universes, and complete strict original
presentation and cylinder lifting identities. The audit also imports the
public `Quillen.Library` boundary.

Evidence is under `logs/boundary-weak-equivalence-independent/`; the verification
script is `logs/verify-boundary-weak-independent.sh`. Source, critical dependency,
and project/toolchain hashes are checked before and after validation.

## Endpoint and limits

`BoundaryLifting.isWeakHomotopyEquivalence` gives the complete empty-aware
property of the original map. Its assumptions contain only genuine strict
finite boundary lifting. The statement supplies neither a global continuous
inverse nor arbitrary compact-pair HELP. Weak-cartesian gluing and the global
relative-realization homotopy-fiber theorem remain separate obligations.
