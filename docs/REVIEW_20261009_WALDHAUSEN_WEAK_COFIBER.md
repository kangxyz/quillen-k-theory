# Independent review: weak cofibrations and actual acyclic cofibers

Date: 2026-10-09. Result: **accepted for the frozen structural endpoint**.
No implementation source was changed.

## Exact contract and hypotheses

For arbitrary independent object/hom universes and any `W : Structure C`,
`Fibration.Acyclic W X` means exactly that the original canonical map from
`W.zero` to `X` belongs to `W.weq`. This is a categorical weak-acyclic predicate;
identification with homological acyclicity in complex categories is a separate
proved specialization.

`ExtensionAxiom W` is an explicit proposition about maps between two actual
cofibration/cofiber pushout squares: weak maps on the source and quotient imply
a weak map on the middle. It contains no realization, fiber, homotopy,
K-equivalence, or desired cofiber-detection conclusion. Despite its name, it is
not a new Lean logical axiom. It is a stated structural hypothesis for the
reverse implication, to be proved in applications.

The accepted theorems establish:

1. Every actual zero object is weakly acyclic, by its unique actual isomorphism
   with `W.zero`.
2. If an actual cofibration is weak, every displayed genuine cofiber is acyclic.
   This direction needs only the existing Waldhausen structure and gluing;
   `ExtensionAxiom` is not required.
3. Conversely, under `ExtensionAxiom W`, an actual cofibration with an acyclic
   displayed cofiber is weak.
4. The resulting iff applies in particular to the already constructed actual
   `ExtensionCategory.cofiber` functor, retaining the original cofibration and
   original chosen-zero map. No alternate quotient is substituted.

Both directions compare the given actual cofiber square with the actual
identity cofiber square. The forward proof applies genuine gluing to identity
source/zero maps and the original weak cofibration. The reverse applies the
structural extension property to the same map of squares. All commutativity
identities follow from the displayed pushout and zero uniqueness. There is no
cylinder, saturation, two-out-of-three, preadditive, abelian, or category-size
restriction beyond the stated ordinary structure and, for the reverse,
structural extension property.

I read the entire source and checked the exact chosen-cofiber specialization
against the previously independently accepted extension-category core. No
conclusion is hidden in the hypotheses beyond the explicitly stated general
extension property.

## Independent verification

The source was rebuilt into an isolated overlay, using the freshly rebuilt
six extension-category core artifacts from my preceding independent review.
Unchanged remaining dependencies are linked. The selected source artifact is
fresh; no production olean was replaced. The check used Lean 4.34.0, `-j1`, and
the shared slot1 lock with acquisition logged.

`audits/FibrationWeakCofiberIndependentAudit.lean` runs a fixed **17-origin**
audit, including private/generated declarations and the structure-generated
constants. Recursive `collectAxioms` permits only `propext`, `Classical.choice`,
and `Quot.sound`. All 17 origins and all consumers pass warning-free.

Consumers retain independent object/hom universes, actual displayed pushouts,
the exact chosen-zero map, and the existing cofiber functor. Added independent
consumers verify the canonical-cofiber forward implication **without** an
extension hypothesis, the reverse implication with that hypothesis explicit,
and agreement of the acyclicity tests for any two actual displayed cofibers.
The frozen source hash matched before and after checking.

## Limits

This is a structural cofiber-detection theorem, not a Waldhausen fibration
or localization theorem. No relative-realization fiber comparison, topological
inverse, based K-map equivalence, or concrete extension-axiom instance is
accepted by this one-file review. The larger route document correctly leaves
those obligations separate. In particular, use on actual complexes requires
an independently proved extension-axiom instance.

## Frozen source and evidence

Source: `Quillen/Waldhausen/Fibration/WeakEquivalenceCofiber.lean`

Source SHA-256:
`c452bbfc85e91815301eb5a0c06ed1c327885e05845dbc98a0e5037e9497fb1c`

Manifest: `logs/fibration-weak-cofiber-independent-20261009/sources.sha256`

Manifest SHA-256:
`e7b72c587acc3743d4f305f68d8d319b865f8d0376911d5ac5760748c3091bc2`

Evidence directory: `logs/fibration-weak-cofiber-independent-20261009/`

- `check.log`: fresh source check
- `audit.log`: fixed17 recursive origin audit and strengthened consumers
- `deps.log`: selected dependency path
- `hashes-before.log`, `hashes-after.log`: frozen source rechecks
- `artifacts.sha256`: exact audit, report, logs and fresh artifact
