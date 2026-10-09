# Weak cofibrations and actual acyclic cofibers

The frozen module `Quillen/Waldhausen/Fibration/WeakEquivalenceCofiber.lean` defines `Fibration.ExtensionAxiom W` as the genuine structural extension condition on two displayed cofiber pushout squares. Its only conclusion is that a map on middle objects is weak when the source and quotient maps are weak. There is no homotopy-theoretic conclusion in the hypothesis.

`Fibration.Acyclic W X` means exactly that the original map from the chosen zero to `X` is weak. The module proves:

- actual zero objects are acyclic;
- `weak_iff_acyclic_of_isPushout`: a cofibration is weak if and only if its displayed actual cofiber is acyclic;
- `cofiber_acyclic_iff`: the same statement for the already constructed actual `ExtensionCategory.cofiber` functor.

The forward implication uses gluing against the identity cofiber square. The reverse implication uses the structural extension axiom on that same square. No cylinder, saturation, realization comparison or fibration conclusion is assumed. Object/hom universes are independent.

Verification: the final direct source check is warning-free; `audits/FibrationWeakCofiberAudit.lean` checks all 17 declaration origins recursively, permitting only `propext`, `Classical.choice`, `Quot.sound`. Its arbitrary-universe consumers retain the displayed quotient square, actual zero-to-object map, original cofibration and existing canonical cofiber. The fixed-count audit passed, as did the frozen source rehash.

Evidence: `logs/fibration-weak-cofiber-sources.sha256`, `logs/fibration-weak-cofiber-final-check.log`, `logs/fibration-weak-cofiber-audit.log`, `logs/fibration-weak-cofiber-rehash.log`, and `logs/fibration-weak-cofiber-artifacts.sha256`.

The next construction route and its genuine remaining obligations are recorded separately in `docs/WALDHAUSEN_FIBRATION_ROUTE.md`. In particular, the relative-realization homotopy-fiber lemma is still a separate theorem to prove.
