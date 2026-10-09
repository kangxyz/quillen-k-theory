# Independent review: original relative-row transitions are weakly cartesian

Both frozen sources in `logs/split-row-transition-cartesian-sources.sha256`
were read completely. **Accepted for this scope.**

The generic proof uses genuine original row-to-simplicial-product homotopy
equivalences and a strictly natural split inclusion. The actual target first
projection, original fiber transition, and source split inclusion compose
literally to identity on the common first factor. Original all-degree
bijections and explicit points give complete weak properties for those
maps. Empty-aware cancellation proves the original fiber transition weak.
No identification of the target chosen basepoint, first-evaluation naturality,
or continuous path choices is assumed.

Under the stated actual connectedness assumptions, accepted fiber detection
proves that the original constant-path homotopy-pullback comparison is weak.
The concrete relative-row instance derives all connectedness and nonemptiness
from the original S-constructions and actual chosen zero, and uses the proved
degreewise relative additivity. The only categorical hypothesis is the genuine
nested weak-equivalence structure, with the explicit common realization
universe. Only tail and split-inclusion outer naturality is used. First-object
evaluation and its coproduct section are not asserted outer-natural.

Both parameter and source coordinates, the complete original constant path,
all finite homotopy maps including degree zero, and component surjectivity are
retained. This supplies the transition-square input for a global fiber proof;
finite weak-cartesian gluing and the diagonal fiber theorem remain open.

## Independent validation

An isolated first-`LEAN_PATH` overlay excludes both target artifact stems.
Both sources were freshly compiled with dependency listings. The fixed11
recursive-origin audit and all12 original consumers passed warning-free;
only `propext`, `Classical.choice`, and `Quot.sound` are admitted recursively.
All original frozen source hashes match before and after the run.

Replay: `logs/verify-split-transition-independent.sh`.
Audit: `audits/SplitRowTransitionIndependentAudit.lean`.
Evidence: `logs/split-transition-independent-*`.
The result is postfreeze work and is outside the 09:45 clean-build archive.
