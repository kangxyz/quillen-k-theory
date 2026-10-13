/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenGrading
public import Quillen.Waldhausen.SConstruction.Iterated.DiagramZeroNull

/-!
# The canonical global coefficient-open localization null

The original restriction-image witness gives zero quotient grade to every actual restricted
native section. The unique arrows from the same joint section zero are therefore weak in
the actual graded Model. Reversing their original realized tracks constructs the whole null
of the original r followed by q, naturally at the same time for every coefficient arrow.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- Unique arrows from the inherited joint zero to the actual native restricted sections. -/
def boundedFlatCoefficientOpenZeroToGraded (a : Under R) :
    (Functor.const (BoundedFlatCoefficientSections (Opposite.op Q, a))).obj
        (boundedFlatCoefficientSectionWaldhausen (Opposite.op P, a)).zero ⟶
      boundedFlatCoefficientOpenRestriction f a where
  app _ := (boundedFlatCoefficientSectionWaldhausen (Opposite.op P, a)).isZero.to_ _
  naturality _ _ _ :=
    (boundedFlatCoefficientSectionWaldhausen (Opposite.op P, a)).isZero.eq_of_src _ _

/-- These original zero-to-image arrows are weak by the constructed restriction-image witness. -/
theorem boundedFlatCoefficientOpenZeroToGraded_weak (a : Under R)
    (S : BoundedFlatCoefficientSections (Opposite.op Q, a)) :
    (boundedFlatCoefficientGradedOpenModel f a).waldhausen.weq
      ((boundedFlatCoefficientOpenZeroToGraded f a).app S) :=
  (boundedFlatCoefficientFullOpenGrading f a).zero.trans
    (boundedFlatCoefficientOpenRestriction_grade_zero f a S).symm

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The reversed zero-to-image realization gives the canonical whole coefficient-natural null. -/
def boundedFlatCoefficientOpenGradingDiagramNull :
    LoopPrespectrum.DiagramNullHomotopy
      (boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f)
      (boundedFlatCoefficientOpenGradingPrespectrumTransformation f) :=
  modelDiagramZeroNull (boundedFlatCoefficientOpenRestrictionModelTransformation f)
    (boundedFlatCoefficientOpenGradingModelTransformation f)
    (fun a ↦ boundedFlatCoefficientOpenZeroToGraded f a)
    (fun a ↦ boundedFlatCoefficientOpenZeroToGraded_weak f a)

/-- Every native coefficient arrow keeps the complete original localization-null time. -/
theorem boundedFlatCoefficientOpenGradingDiagramNull_coefficient
    {a b : Under R} (g : a ⟶ b) (n : ℕ) (s : unitInterval)
    (x : ((boundedFlatCoefficientOpenPrespectrumFunctor f).obj a).space n) :
    ((boundedFlatCoefficientGradedOpenPrespectrumFunctor f).map g).map n
        (((boundedFlatCoefficientOpenGradingDiagramNull f).homotopy a).level n (s, x)) =
      ((boundedFlatCoefficientOpenGradingDiagramNull f).homotopy b).level n
        (s, ((boundedFlatCoefficientOpenPrespectrumFunctor f).map g).map n x) :=
  (boundedFlatCoefficientOpenGradingDiagramNull f).naturality g n s x

end Quillen.PerfectComplexes
