# The extension axiom for the original coarse quotient rows

`Fibration.Rows.ExtensionAxiom` proves
`RowWeakEquivalences.extensionAxiom N he n` from the genuine base axiom
`he : ExtensionAxiom N.coarse`. The row objects, cofibrations, maps, and
pointwise coarse weak class are the unchanged accepted same-type structure.

The original displayed cofiber square is genuinely a component pushout,
by the accepted pointwise-pushout theorem along actual Reedy cofibrations.
Only the actual zero corner is replaced by its canonical isomorphism to the
chosen coarse zero. The base extension axiom is applied to the original
component maps and the evaluated original commuting squares. This proves
coarse weakness of the unchanged middle map at every interval.

Object and hom universes are independent. No saturation, cylinder, closure
under cones or shifts, row equivalence, or realization hypothesis is needed.
The actual complex-subcategory case follows from the accepted homology
extension theorem. The audit includes this case, bounded terms without
kernel closure, arbitrary schemes, original component diagrams, and degree
zero.

The focused source check passed warning-free. Both initial and final fixed2
recursive audits passed, with only `propext`, `Classical.choice`, and
`Quot.sound`. All eight consumers passed; pre/post source hashes match.
Independent review is separate and pending.

- Frozen manifest: `logs/row-extension-axiom-sources.sha256`
- Audit: `audits/RowExtensionAxiomAudit.lean`
- Source log: `logs/row-extension-axiom-check.log` (empty)
- Terminal audit: `logs/row-extension-axiom-audit-final.log`
- Evidence: `logs/row-extension-axiom-artifacts.sha256`
