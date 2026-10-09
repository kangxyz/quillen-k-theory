# The actual acyclic subcategory for nested weak equivalences

`Quillen/Waldhausen/Fibration/AcyclicSubcategory.lean` constructs the full subcategory on genuine coarse-acyclic objects with the inherited **fine** Waldhausen weak equivalences. Object and hom universes are independent.

## Explicit input

`NestedWeakEquivalences V` consists only of a genuine coarse Waldhausen structure, equality of its cofibration and chosen-zero data with those of `V`, and the inclusion `V.weq ≤ coarse.weq`. No fiber or equivalence conclusion occurs in this input.

`AcyclicCategory N` is the actual full subcategory on `coarse.weq (coarse.isZero.to_ X)`. Its `acyclicStructure` has literal inverse-image cofibrations and fine weak equivalences. Its chosen zero maps to `V.zero` definitionally, and to the coarse zero by the input equality.

## Derived structure

- Repleteness follows from composition with an actual isomorphism.
- A pushout of three acyclic objects along a cofibration is acyclic by coarse gluing against the all-zero pushout square.
- Fine pushouts therefore exist inside the actual full subcategory.
- Every arbitrary displayed inherited pushout along a cofibration is the genuine ambient pushout: compare it with the constructed one by the unique pushout isomorphism.
- The inherited cofibration and fine weak-equivalence axioms, including gluing, follow from these actual ambient squares.
- `acyclicInclusion_exact`, `changeWeak_exact`, and `acyclicInclusion_coarse_exact` prove structural exactness of the original inclusion and identity change-of-weak-class functors.
- `fine_cofiber_acyclic` separately proves closure of the existing actual fine cofiber, with no new quotient substituted.

Neither construction of the inherited structure nor quotient closure requires saturation or the extension axiom. Saturation is used only in the separate `acyclicInclusion_map_coarse_weak`: every morphism between coarse-acyclic objects becomes coarse-weak by two-out-of-three. This does not replace the inherited fine weak-equivalence class.

## Verification

The source is frozen in `logs/fibration-acyclic-subcategory-sources.sha256`. The final direct source check passed without warnings. `audits/FibrationAcyclicSubcategoryAudit.lean` checks all 48 declaration origins recursively against the standard three foundational axioms and tests actual predicate/cofibration/fine-weak formulas, unchanged inclusion maps, both zero identifications, exactness, arbitrary displayed pushouts, and the original fine cofiber. Source hashes were rechecked successfully.

Logs and hashes are in `logs/fibration-acyclic-subcategory-{final-check,audit,rehash}.log` and `logs/fibration-acyclic-subcategory-artifacts.sha256`. The previously frozen weak-cofiber and extension sources are unchanged. This is the structural acyclic category, not the relative-realization fibration theorem.
