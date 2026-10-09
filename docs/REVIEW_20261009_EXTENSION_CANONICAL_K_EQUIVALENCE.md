# Independent acceptance: canonical extension-category K-equivalence

Accepted 2026-10-09 06:49 UTC after full semantic inspection, fresh isolated
rebuild of both sources, fixed15 recursive-origin audit, exact-map consumers
including n=0, and matching source hashes. All checks are warning-free.

The concrete theorem `ExtensionCategory.KEquiv W n` is a group equivalence
from the genuine extension-category K-group to the K-group of the actual
product Waldhausen category. Its forward homomorphism is definitionally the
original `KMap (sourceCofiber_exact W) n`. Its inverse is proved equal to
`splitKMap W n`, the original canonical K-map of the actual split extension.
Coproduct existence is derived from the Waldhausen axioms.

The small generic adapter first retains an actual exact-functor realization
homotopy equivalence under its concrete canonical zero-normalization natural
isomorphism. The normalized forward map is literally the map used by the
existing KMap definition, so the proved forward-based homotopy-group theorem
applies. It does not require a based inverse. For the concrete extension
endpoint, the realization equivalence is the independently proved actual
source/cofiber equivalence, not an assumed comparison. The exact inverse is
identified using the original split-cofiber natural isomorphism and the proved
KMap identity/composition laws.

The generic adapter permits independent object and hom universes. The concrete
extension endpoint honestly uses C : Type u, Category.{u} C, matching its
realization proof. It targets K(C × C), not yet an identified product K(C) × K(C).
The latter requires a separate actual realization-product homotopy-group bridge.
No general fundamental-group commutativity or based inverse homotopy is assumed.

Evidence: `audits/WaldhausenExtensionKEquivalenceIndependentAudit.lean` and
`logs/extension-kequiv-independent-*`. The fresh overlay is
`/tmp/quillen-extension-kequiv-independent-0641`, first in LEAN_PATH; the audit's
import-resolution log confirms both source-origin artifacts. The manifest
`logs/waldhausen-extension-kequivalence-sources.sha256` contains exactly the
reviewed generic and concrete files. Recursive axiom closure includes private
and generated declarations and permits only propext, Classical.choice and
Quot.sound. This endpoint does not establish the change-of-weak-equivalences
fibration, Gillet–Waldhausen, strict/local-perfect comparison or TT localization.
