/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionAcyclicComparison
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumZeroNaturality

/-!
# Evaluation of the original supported-section null track

The actual inherited-zero inclusion square transports the entire original weak
zero-to-section transformation. Its reversed homotopy agrees at every parameter with the
original geometric acyclic null track. No endpoint-only replacement or time change is used.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open Waldhausen Waldhausen.Fibration Waldhausen.IteratedS
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation
  boundedFlatAffineSupportedSectionEquivalence boundedFlatAffineSupportedEvaluation

/-- Original evaluation preserves every value of the unchanged support-restriction null track. -/
theorem boundedFlatAffineSupportedSectionOpenNullHomotopy_evaluation (n : ℕ) (s : unitInterval)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSectionOpenEvaluationPrespectrumMap j).map n
        ((boundedFlatAffineSupportedSectionOpenNullHomotopy j).level n (s, x)) =
      (acyclicPrespectrumNullhomotopy (boundedFlatPerfectOpenNested j)).level n
        (s, (boundedFlatAffineSupportedSectionAcyclicPrespectrumMap j).map n x) := by
  let N := boundedFlatPerfectOpenNested j
  let F := boundedFlatAffineSupportedSectionForgetModelMap j ≫
    boundedFlatAffineSectionOpenModelMap j
  let G := modelMap (acyclicStructure N) N.coarse (acyclicInclusion_coarse_exact N)
    (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm)
  let a := boundedFlatAffineSupportedSectionAcyclicModelMap j
  let b := boundedFlatAffineSectionOpenEvaluationModelMap j
  have hs : F ≫ b = a ≫ G := by
    apply Model.Hom.ext
    apply smallModelFunctor_square F.functor (boundedFlatAffineOriginalEvaluation R)
      (boundedFlatAffineSupportedSectionAcyclicEvaluation j) (acyclicInclusion N)
    exact (congrArg (fun K => K ⋙ boundedFlatAffineOriginalEvaluation R)
      (CategoryTheory.Functor.comp_id (boundedFlatAffineSectionSupported j).ι)).trans
        (boundedFlatAffineSupportedSectionAcyclicEvaluation_inclusion j).symm
  let θ : (zeroHom (modelOf (acyclicStructure N)) (modelOf N.coarse)).functor ⟶ G.functor :=
    whiskerLeft AsSmall.down (whiskerRight (zeroToAcyclicInclusion N) AsSmall.up)
  have hθ : ∀ A, (modelOf N.coarse).waldhausen.weq (θ.app A) :=
    fun A => zeroToAcyclicInclusion_weak N (AsSmall.down.obj A)
  have h := prespectrumZeroTransformationHomotopy_naturality F G a b hs
    (boundedFlatAffineSupportedSectionZeroToOpen j) θ
    (boundedFlatAffineSupportedSectionZeroToOpen_weak j) hθ n
  exact congrArg (fun H => H (unitInterval.symm s, x)) h

end Quillen.PerfectComplexes
