/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionWaldhausen

/-!
# Strict coefficient reindexing is genuinely Waldhausen-exact

Literal original evaluation after reindexing identifies it with evaluation at the actual
coefficient arrow. The proved original evaluation equivalence reflects pushouts; zero
preservation retains the same pointwise chosen-zero sections.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- Every actual coefficient restriction is exact for the genuine pointwise Waldhausen structures.
-/
theorem boundedFlatAffineSectionsMap_exact {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    Waldhausen.IsExact (boundedFlatAffineSectionWaldhausen R).cof
      (boundedFlatAffineSectionWaldhausen R).weq
      (boundedFlatAffineSectionWaldhausen S).cof (boundedFlatAffineSectionWaldhausen S).weq
      (boundedFlatAffineSectionsMap φ) where
  zero h := by
    have hz : IsZero ((boundedFlatAffineSectionsMap φ).obj (boundedFlatAffineSectionZero R)) := by
      rw [boundedFlatAffineSectionsMap_sectionZero]
      exact isZero_boundedFlatAffineSectionZero S
    exact hz.of_iso ((boundedFlatAffineSectionsMap φ).mapIso
      (h.iso (isZero_boundedFlatAffineSectionZero R)))
  cofibration a ha := by
    change (boundedFlatPerfectWaldhausen (Spec S)).cof
      ((boundedFlatAffineSectionsMap φ ⋙ boundedFlatAffineOriginalEvaluation S).map a)
    rw [boundedFlatAffineSectionsMap_comp_evaluation]
    exact (boundedFlatAffineEvaluationAt_exact R (Under.mk φ)).cofibration a ha
  weak a ha := by
    change (boundedFlatPerfectWaldhausen (Spec S)).weq
      ((boundedFlatAffineSectionsMap φ ⋙ boundedFlatAffineOriginalEvaluation S).map a)
    rw [boundedFlatAffineSectionsMap_comp_evaluation]
    exact (boundedFlatAffineEvaluationAt_exact R (Under.mk φ)).weak a ha
  pushout {A B D P} {i f g j} hi h := by
    apply IsPushout.of_map_of_faithful (boundedFlatAffineOriginalEvaluation S)
    change IsPushout
      ((boundedFlatAffineSectionsMap φ ⋙ boundedFlatAffineOriginalEvaluation S).map i)
      ((boundedFlatAffineSectionsMap φ ⋙ boundedFlatAffineOriginalEvaluation S).map f)
      ((boundedFlatAffineSectionsMap φ ⋙ boundedFlatAffineOriginalEvaluation S).map g)
      ((boundedFlatAffineSectionsMap φ ⋙ boundedFlatAffineOriginalEvaluation S).map j)
    rw [boundedFlatAffineSectionsMap_comp_evaluation]
    exact (boundedFlatAffineEvaluationAt_exact R (Under.mk φ)).pushout hi h

end Quillen.PerfectComplexes
