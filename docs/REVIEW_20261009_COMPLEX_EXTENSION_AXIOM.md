# Independent review: the actual quasi-isomorphism extension axiom

Date: 2026-10-09. Result: **accepted for the frozen two-source structural endpoint**.
No implementation source was changed.

## Mathematical contract

`Quillen.quasiIso_middle_of_shortExact` accepts two actual short exact sequences
of cochain complexes in an arbitrary abelian category, a morphism between them,
and quasi-isomorphisms on its two outer components. It proves that the original
middle component is a quasi-isomorphism. Object and hom universes are independent.

The proof uses the actual neighboring long homology sequences. The four-lemma
argument with degrees `(n-1,n)` proves the middle homology map monic; the argument
with `(n,n+1)` proves it epic. In the abelian target it is therefore an isomorphism
in every degree. No extension property or desired middle-map conclusion is an input.

For a displayed zero-corner pushout in an abelian category, the original quotient
projection is proved to be a categorical cokernel by an explicit universal
property. With the original source map monic, the actual displayed sequence is
short exact. These constructions derive `complexes_extensionAxiom` for ordinary
complexes with monomorphism cofibrations and genuine quasi-isomorphisms.

`complexSubcategory_extensionAxiom P` accepts the actual full complex subcategory
with `P.ContainsZero`, repleteness, inherited exact extension closure, and
`P.IsClosedUnderFiniteProducts`. The finite-product assumption is explicit in
this theorem's interface. Arbitrary displayed inherited cofibration pushouts are
transported to actual ambient pushouts by the existing proved inclusion theorem;
no ambient pushout preservation is assumed. The original three component maps
are used in the resulting short exact sequences. No kernel, cone, shift, or
acyclic-cycle closure is needed. The structural extension axiom is a conclusion.

I read both complete sources and checked their usage of the previously reviewed
weak-cofiber interface and actual full-subcategory pushout preservation. The
accepted concrete cofiber iff retains `ExtensionCategory.cofiber` and the actual
canonical map from the chosen zero.

## Independent verification

Both sources were rebuilt in order into an isolated overlay, with the previously
independently rebuilt weak-cofiber dependency. Other unchanged dependencies were
linked. No production artifact was replaced. Lean 4.34.0 ran with `-j1` under the
shared slot1 lock; acquisition is recorded in
`logs/complex-acyclic-independent-session.log`.

`audits/ComplexExtensionIndependentAudit.lean` checks exactly **9 defining-module
origins**, including generated/private declarations. Recursive `collectAxioms`
allows only `propext`, `Classical.choice`, and `Quot.sound`. All origins passed.
Independent-universe consumers check the middle quasi-isomorphism, both actual
extension axioms, and the actual chosen-cofiber iff. Added independent consumers
check the original displayed quotient projection's categorical cokernel and
short exactness. Source and audit checks passed warning-free. Source hashes match
before and after verification.

## Scope limits

This supplies the concrete structural extension property needed by the preceding
cofiber-detection theorem. It does not prove a Waldhausen fibration, relative
realization comparison, localization equivalence, or Gillet–Waldhausen theorem.

## Frozen sources and evidence

- `Quillen/Algebra/Homology/QuasiIsoExtension.lean`:
  `acfe5321ecce37d89d2fac51c7f9eedd174c6fe8246ef379a6f4f2c1969da22b`
- `Quillen/Waldhausen/Fibration/ComplexExtension.lean`:
  `3463a187ed7c9de63a976115d9b3b5c19020c3dab69e6ee1efd0b94c4f942662`

Evidence directory: `logs/complex-extension-independent-20261009/`.
`sources.sha256`, `check.log`, `audit.log`, `deps.log`, `hashes-before.log`, and
`hashes-after.log` record the frozen boundary and fresh checks. `artifacts.sha256`
records this report, the independent audit, logs, and fresh oleans.
