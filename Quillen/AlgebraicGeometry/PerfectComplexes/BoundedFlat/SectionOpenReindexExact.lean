/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenStructure
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionReindexExact
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionCoefficientIso
public import Quillen.Waldhausen.ExtensionCategory.ExactTransport

/-!
# Original coefficient reindexing for relative-open sections

The genuine geometric pullback along an arbitrary commuting open-pair square is exact.
The actual original evaluation-transition isomorphism transports that exactness to arrow
evaluation. Literal coefficient reindexing therefore preserves the original coarse weak class,
as well as the unchanged fine cofibrations, zero and pushouts. No cartesian or flatness premise
is needed, and geometric evaluation remains naturally isomorphic rather than strictly natural.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)
attribute [local irreducible] boundedFlatAffineOriginalEvaluation boundedFlatAffineEvaluationAt

include l h in
/-- The original coefficient-arrow evaluation is exact for the actual relative-open structures. -/
theorem boundedFlatAffineEvaluationAt_open_exact :
    Waldhausen.IsExact (boundedFlatAffineSectionOpenWaldhausen j).cof
      (boundedFlatAffineSectionOpenWaldhausen j).weq
      (boundedFlatPerfectOpenWaldhausen j').cof (boundedFlatPerfectOpenWaldhausen j').weq
      (boundedFlatAffineEvaluationAt R (Under.mk f)) :=
  Waldhausen.ExtensionCategory.isExact_of_natIso
    (boundedFlatAffineSectionOpenWaldhausen j) (boundedFlatPerfectOpenWaldhausen j')
    ((boundedFlatAffineSectionOpenEvaluation_coarse_exact j).comp
      (boundedFlatPerfectOpenPullback_exact (boundedFlatAffineSupportedPairSquare j j' f l h)))
    (boundedFlatAffineEvaluationPullbackIso R (Under.mk f))

include l h in
/-- The unchanged coefficient functor is exact for every specified original open-pair square. -/
theorem boundedFlatAffineSectionsMap_open_exact :
    Waldhausen.IsExact (boundedFlatAffineSectionOpenWaldhausen j).cof
      (boundedFlatAffineSectionOpenWaldhausen j).weq
      (boundedFlatAffineSectionOpenWaldhausen j').cof
      (boundedFlatAffineSectionOpenWaldhausen j').weq (boundedFlatAffineSectionsMap f) where
  zero := (boundedFlatAffineSectionsMap_exact f).zero
  cofibration := (boundedFlatAffineSectionsMap_exact f).cofibration
  pushout := (boundedFlatAffineSectionsMap_exact f).pushout
  weak a ha := by
    change (boundedFlatPerfectOpenWaldhausen j').weq
      ((boundedFlatAffineSectionsMap f ⋙ boundedFlatAffineOriginalEvaluation S).map a)
    rw [boundedFlatAffineSectionsMap_comp_evaluation]
    exact (boundedFlatAffineEvaluationAt_open_exact j j' f l h).weak a ha

end Quillen.PerfectComplexes
