# Original all-acyclic category and coarse inclusion

Two separate categorical modules extend the accepted all-weak boundary.

`AllWeak/AcyclicEquivalence.lean` gives the actual equivalence from
`AcyclicCategory (AllWeak.nested W)` to the original C. Its forward functor
is the existing acyclic inclusion. Its inverse sends X to `⟨X,trivial⟩` and
retains every original morphism. Both composites are strict functor
equalities, both functors are genuinely exact for the inherited fine weak
class, and both chosen zeros are preserved literally. Cofibrations and fine
weak maps are detected on the unchanged original maps. The new coarse
all-weak class is not substituted for the inherited fine weak class.

`AllWeak/AcyclicInclusion.lean` proves the original acyclic inclusion exact
from `AllWeak.waldhausenStructure (acyclicStructure N)` to N.coarse. The
only extra structural hypothesis is coarse two-out-of-three, which proves
weakness of every actual acyclic-to-acyclic arrow. The original simplicial
and continuous change-of-weak/inclusion triangles are strict equalities.
The original zero-to-identity component maps to the original
zero-to-acyclic-inclusion component, with exactly N's chosen-zero equality
inserted; that component statement itself does not require saturation.

All these statements retain independent object and morphism universes.
No ordinarySRows transport, double-S equivalence, global fiber theorem, or
realized nullhomotopy-coherence theorem is claimed. The pointwise
transformation identity is an actual input for that later coherence proof,
not its replacement.

Verification: the two source checks are warning-free. The recursive
source-origin audit and actual-map consumers are in
`audits/AllWeakAcyclicAudit.lean`; the final fixed22 audit (17 equivalence +5 inclusion origins) and all19
consumers pass warning-free in `logs/all-weak-acyclic-audit-final.log`.
Recursive axioms are standard-only; source hashes are frozen in
`logs/all-weak-acyclic-sources.sha256`. Independent review passed: fresh two-source rebuild, fixed22 origins and25
strengthened consumers, warning-free with hashes unchanged. The original three all-weak sources remain unchanged.
