/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionDiagram
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionGradingPrespectrum
public import Quillen.AlgebraicGeometry.PerfectComplexes.PairRestriction
public import Quillen.Waldhausen.SConstruction.Iterated.DiagramZeroNull

/-!
# The canonical full-open section localization null

The actual restricted section has zero grade by its original evaluated weak-image witness.
The unique arrows from the inherited section zero are therefore weak in the actual graded
Model. Reversing this same zero-to-image transformation constructs the whole null of the
original restriction followed by change of weakness. Its entire track is coefficient-natural.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.AlgebraicGrothendieck
open Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation
  boundedFlatAffineFullOpenOriginalEvaluation boundedFlatAffineFullOpenSectionRestriction
  boundedFlatPerfectPseudofunctor boundedFlatAffineFullOpenPseudofunctor
  boundedFlatAffineFullOpenRestrictionStrongTrans

/-- The actual restricted section has zero quotient grade by its original perfect image witness. -/
theorem boundedFlatAffineFullOpenSectionRestriction_grade_zero
    (a : Under R) (S : BoundedFlatAffineSections a.right) :
    (boundedFlatAffineFullOpenSectionGrading j a).value
      ((boundedFlatAffineFullOpenSectionRestriction j a).obj S) = 0 := by
  rw [boundedFlatAffineFullOpenSectionGrading_value]
  change (perfectOpenDeficitGrading (inclusion j a)).value
    ((boundedFlatPerfectInclusion (openSpace j a)).obj
      ((boundedFlatAffineFullOpenOriginalEvaluation j a).obj
        ((boundedFlatAffineFullOpenSectionRestriction j a).obj S))) = 0
  have he := Functor.congr_obj (boundedFlatAffineFullOpenSectionRestriction_comp_evaluation j a) S
  simp only [Functor.comp_obj] at he
  rw [he]
  apply imageQuotientGrading_zero_of_weakImage
  let e := (boundedFlatPerfectOriginalRestrictionIso (inclusion j a)).app
    ((boundedFlatAffineOriginalEvaluation a.right).obj S)
  refine ⟨(boundedFlatPerfectInclusion (Spec a.right)).obj
      ((boundedFlatAffineOriginalEvaluation a.right).obj S), e.hom, ?_⟩
  exact (perfectWaldhausen (openSpace j a)).weq_iso e.hom (show IsIso e.hom from inferInstance)

/-- The unique arrows from the inherited whole chosen zero to the unchanged restricted sections. -/
def boundedFlatAffineFullOpenSectionZeroToGraded (a : Under R) :
    (Functor.const (BoundedFlatAffineSections a.right)).obj
        (boundedFlatAffineFullOpenSectionWaldhausen j a).zero ⟶
      boundedFlatAffineFullOpenSectionRestriction j a where
  app _ := (boundedFlatAffineFullOpenSectionWaldhausen j a).isZero.to_ _
  naturality _ _ _ := (boundedFlatAffineFullOpenSectionWaldhausen j a).isZero.eq_of_src _ _

/-- The original zero-to-image arrows are weak by the genuine original image quotient relation. -/
theorem boundedFlatAffineFullOpenSectionZeroToGraded_weak (a : Under R)
    (S : BoundedFlatAffineSections a.right) :
    (boundedFlatAffineFullOpenGradedSectionModel j a).waldhausen.weq
      ((boundedFlatAffineFullOpenSectionZeroToGraded j a).app S) :=
  (boundedFlatAffineFullOpenSectionGrading j a).zero.trans
    (boundedFlatAffineFullOpenSectionRestriction_grade_zero j a S).symm

variable [CompactSpace U]

/-- The reversed zero-to-image tracks give a whole null on the original coefficient diagrams. -/
def boundedFlatAffineFullOpenSectionGradingDiagramNull :
    LoopPrespectrum.DiagramNullHomotopy
      (boundedFlatAffineSectionFullOpenPrespectrumTransformation j)
      (boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j) :=
  modelDiagramZeroNull (boundedFlatAffineSectionFullOpenModelTransformation j)
    (boundedFlatAffineFullOpenSectionGradingModelTransformation j)
    (fun a => boundedFlatAffineFullOpenSectionZeroToGraded j a)
    (fun a => boundedFlatAffineFullOpenSectionZeroToGraded_weak j a)

/-- The same constructed null has the literal original restriction and grading endpoints. -/
def boundedFlatAffineFullOpenSectionGradingNullHomotopy (a : Under R) :
    LoopPrespectrum.Homotopy
      (prespectrumMap (boundedFlatAffineSectionFullOpenModelMap j a) ≫
        (boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j).app a)
      (LoopPrespectrum.zeroHom
        ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a)
        ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a)) :=
  (boundedFlatAffineFullOpenSectionGradingDiagramNull j).homotopy a

/-- Every coefficient arrow preserves the entire original null at the identical time. -/
theorem boundedFlatAffineFullOpenSectionGradingNullHomotopy_coefficient
    {a b : Under R} (f : a ⟶ b) (n : ℕ) (s : unitInterval)
    (x : ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a).space n) :
    ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map f).map n
        ((boundedFlatAffineFullOpenSectionGradingNullHomotopy j a).level n (s, x)) =
      (boundedFlatAffineFullOpenSectionGradingNullHomotopy j b).level n
        (s, ((boundedFlatAffineSectionOpenPrespectrumFunctor j).map f).map n x) :=
  (boundedFlatAffineFullOpenSectionGradingDiagramNull j).naturality f n s x

end Quillen.PerfectComplexes
