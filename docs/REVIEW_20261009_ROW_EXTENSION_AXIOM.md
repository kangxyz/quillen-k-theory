# Independent review: the actual coarse-row extension axiom

Reviewed the frozen `Quillen/Waldhausen/Fibration/Rows/ExtensionAxiom.lean`
and the actual pointwise-pushout/coarse-row prerequisites. Its two declarations
have the stated minimal hypotheses; no semantic issue was found.

`cofiber_evaluation_isPushout` evaluates a displayed original row cofiber
square using the actual Reedy cofibration hypothesis and the proved row
pushout evaluation theorem. It changes only the zero corner by the genuine
isomorphism from the fine chosen zero to the coarse chosen zero. Both
original nonzero arrows are unchanged.

`extensionAxiom` then applies the structural base coarse extension axiom at
every original interval, with the evaluated actual cofibration evidence,
the same original side/middle maps, and their original commutative squares.
The conclusion is exactly pointwise coarse weakness of that middle map.

No saturation, cylinder, cone/shift/kernel closure, presentation equivalence,
or fibration hypothesis is used. Object and morphism universes are independent.
The construction iterates on actual row categories and applies to actual
complex subcategories through their already-proved structural extension axiom.

## Independent verification

`logs/row-extension-axiom-independent/verify.sh` creates a fresh project overlay
that initially excludes every target artifact. The nested-row prerequisite
is the independently rebuilt artifact from its accepted review, rather than
a target-derived live copy. The extension source is rebuilt and the audit
uses that fresh result. Sources and dependency artifacts are hashed separately.

`audits/RowExtensionAxiomIndependentAudit.lean` checks all2 defining origins
recursively with a fixed2 guard. It retains the author's8 consumers and adds
actual iterated-row extension and the original displayed row-cofiber
weakness/acyclicity characterization. The consumers include independent
universes, original arrows, degree0, actual complex/bounded-term models and
arbitrary schemes, without cone/shift/kernel assumptions.

**Accepted.** Fresh target rebuild, fixed2 recursive origin audit and all10
consumers passed warning-free, with only the standard three axioms. Target
pre/post hashes, the29-module Quillen source closure, and34 used dependency
artifacts all match. The frozen source was not changed.
