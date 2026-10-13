/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenGrading
public import Quillen.Waldhausen.SConstruction.Iterated.DiagramZeroNull

/-!
# The canonical supported native coefficient localization null

The actual supported restriction has zero grade in its original supported
image quotient. Unique arrows from the same supported joint zero are therefore
weak in G_Z. Reversing their original realization gives the whole null of the
original r_Z followed by q_Z, with the same null time for every coefficient
arrow. The coefficient diagrams require compact P and Q; no quasi-separated
or auxiliary-complement compactness premise is used to construct this null.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Unique arrows from the inherited supported joint zero to actual supported restrictions. -/
def boundedFlatCoefficientSupportedOpenZeroToGraded (a : Under R) :
    (Functor.const (BoundedFlatCoefficientSupportedAmbientSections (Q := Q) T a)).obj
        (boundedFlatCoefficientSupportedSectionWaldhausen
          (boundedFlatCoefficientOpenSupportOpen f T a).ι).zero ⟶
      boundedFlatCoefficientSupportedOpenRestriction f T a where
  app _ := (boundedFlatCoefficientSupportedSectionWaldhausen
    (boundedFlatCoefficientOpenSupportOpen f T a).ι).isZero.to_ _
  naturality _ _ _ := (boundedFlatCoefficientSupportedSectionWaldhausen
    (boundedFlatCoefficientOpenSupportOpen f T a).ι).isZero.eq_of_src _ _

/-- These actual zero-to-image arrows are weak by the original supported restriction witness. -/
theorem boundedFlatCoefficientSupportedOpenZeroToGraded_weak (a : Under R)
    (S : BoundedFlatCoefficientSupportedAmbientSections (Q := Q) T a) :
    (boundedFlatCoefficientSupportedGradedOpenModel f T a).waldhausen.weq
      ((boundedFlatCoefficientSupportedOpenZeroToGraded f T a).app S) :=
  (boundedFlatCoefficientSupportedFullOpenGrading f T a).zero.trans
    (boundedFlatCoefficientSupportedOpenRestriction_grade_zero f T a S).symm

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- Reversed zero-to-image realization constructs the original coefficient-natural supported null.
-/
def boundedFlatCoefficientSupportedOpenGradingDiagramNull :
    LoopPrespectrum.DiagramNullHomotopy
      (boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T)
      (boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T) :=
  modelDiagramZeroNull (boundedFlatCoefficientSupportedOpenRestrictionModelTransformation f T)
    (boundedFlatCoefficientSupportedOpenGradingModelTransformation f T)
    (fun a ↦ boundedFlatCoefficientSupportedOpenZeroToGraded f T a)
    (fun a ↦ boundedFlatCoefficientSupportedOpenZeroToGraded_weak f T a)

/-- Every original coefficient arrow preserves the whole supported localization-null time. -/
theorem boundedFlatCoefficientSupportedOpenGradingDiagramNull_coefficient
    {a b : Under R} (g : a ⟶ b) (n : ℕ) (s : unitInterval)
    (x : ((boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a).space n) :
    ((boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).map g).map n
        (((boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a).level n (s, x)) =
      ((boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy b).level n
        (s, ((boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T).map g).map n x) :=
  (boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).naturality g n s x

end Quillen.PerfectComplexes
