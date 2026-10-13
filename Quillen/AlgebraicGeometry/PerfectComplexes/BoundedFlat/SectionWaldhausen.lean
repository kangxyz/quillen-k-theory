/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionZero
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionMorphismClasses
public import Quillen.Waldhausen.EquivalenceStructure

/-!
# The actual pointwise Waldhausen structure on bounded-flat sections

The categorical evaluation equivalence constructs the pushouts. Its inverse-image morphism
classes are proved to be exactly the actual pointwise classes, with the original chosen-zero
section retained. Evaluation at every arrow and strict coefficient restriction are exact.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- Genuine section Waldhausen structure, retaining the original pointwise chosen zero. -/
def boundedFlatAffineSectionWaldhausen (R : CommRingCat.{u}) :
    Waldhausen.Structure (BoundedFlatAffineSections R) :=
  (boundedFlatPerfectWaldhausen (Spec R)).ofEquivalence
    (boundedFlatAffineSectionEquivalence R) (boundedFlatAffineSectionZero R) (by
      change IsZero ((boundedFlatAffineOriginalEvaluation R).obj (boundedFlatAffineSectionZero R))
      rw [boundedFlatAffineOriginalEvaluation_sectionZero]
      exact (boundedFlatPerfectWaldhausen (Spec R)).isZero)

/-- The actual cofibrations are exactly the original pointwise cofibrations. -/
theorem boundedFlatAffineSectionWaldhausen_cof_iff (R : CommRingCat.{u})
    {s t : BoundedFlatAffineSections R} (a : s ⟶ t) :
    (boundedFlatAffineSectionWaldhausen R).cof a ↔ boundedFlatAffineSectionCof R a :=
  (boundedFlatAffineSectionCof_iff R a).symm

/-- The actual weak equivalences are exactly the original pointwise weak equivalences. -/
theorem boundedFlatAffineSectionWaldhausen_weq_iff (R : CommRingCat.{u})
    {s t : BoundedFlatAffineSections R} (a : s ⟶ t) :
    (boundedFlatAffineSectionWaldhausen R).weq a ↔ boundedFlatAffineSectionWeq R a :=
  (boundedFlatAffineSectionWeq_iff R a).symm

/-- The original identity evaluation is genuinely Waldhausen-exact. -/
theorem boundedFlatAffineOriginalEvaluation_exact (R : CommRingCat.{u}) :
    Waldhausen.IsExact (boundedFlatAffineSectionWaldhausen R).cof
      (boundedFlatAffineSectionWaldhausen R).weq
      (boundedFlatPerfectWaldhausen (Spec R)).cof (boundedFlatPerfectWaldhausen (Spec R)).weq
      (boundedFlatAffineOriginalEvaluation R) :=
  Waldhausen.Structure.ofEquivalence_exact _ _ _ _

/-- Every actual coefficient-arrow evaluation is exact, by original geometric pullback. -/
theorem boundedFlatAffineEvaluationAt_exact (R : CommRingCat.{u}) (j : Under R) :
    Waldhausen.IsExact (boundedFlatAffineSectionWaldhausen R).cof
      (boundedFlatAffineSectionWaldhausen R).weq
      (boundedFlatPerfectWaldhausen (Spec j.right)).cof
      (boundedFlatPerfectWaldhausen (Spec j.right)).weq
      (boundedFlatAffineEvaluationAt R j) where
  zero h := ((boundedFlatPerfectPullback_exact (Spec.map j.hom)).zero
    ((boundedFlatAffineOriginalEvaluation_exact R).zero h)).of_iso
      ((boundedFlatAffineEvaluationPullbackIso R j).app _).symm
  cofibration a h := ((boundedFlatAffineSectionWaldhausen_cof_iff R a).mp h) j
  weak a h := ((boundedFlatAffineSectionWaldhausen_weq_iff R a).mp h) j
  pushout hi h := by
    have hp := (boundedFlatPerfectPullback_exact (Spec.map j.hom)).pushout
      ((boundedFlatAffineOriginalEvaluation_exact R).cofibration _ hi)
      ((boundedFlatAffineOriginalEvaluation_exact R).pushout hi h)
    let e := boundedFlatAffineEvaluationPullbackIso R j
    exact hp.of_iso (e.app _) (e.app _) (e.app _) (e.app _)
      (e.hom.naturality _) (e.hom.naturality _) (e.hom.naturality _) (e.hom.naturality _)

/-- The chosen Waldhausen zero is the source-independent pointwise zero section. -/
theorem boundedFlatAffineSectionWaldhausen_zero (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionWaldhausen R).zero = boundedFlatAffineSectionZero R := rfl

/-- The actual inverse of the proved evaluation equivalence is also Waldhausen-exact. -/
theorem boundedFlatAffineSectionEquivalence_inverse_exact (R : CommRingCat.{u}) :
    Waldhausen.IsExact (boundedFlatPerfectWaldhausen (Spec R)).cof
      (boundedFlatPerfectWaldhausen (Spec R)).weq
      (boundedFlatAffineSectionWaldhausen R).cof (boundedFlatAffineSectionWaldhausen R).weq
      (boundedFlatAffineSectionEquivalence R).inverse :=
  Waldhausen.Structure.ofEquivalence_inverse_exact _ _ _ _

end Quillen.PerfectComplexes
