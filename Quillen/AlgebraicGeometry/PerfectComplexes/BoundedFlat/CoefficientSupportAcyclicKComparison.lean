/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportLocalizationModels
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenCofinality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OpenFibration

/-!
# The original supported and acyclic coefficient K-evaluations

The actual coefficient support-to-acyclic evaluation induces precisely the
original supported section K-equivalence followed by the inverse geometric
acyclic-to-supported K-equivalence. Its inverse therefore carries the original
geometric change-of-weak-equivalence boundary to the existing supported
bounded-flat boundary followed by inverse section evaluation. These comparisons
hold in every nonnegative degree without any compactness hypothesis.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.Fibration
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedFlatCoefficientSupportedEvaluation
  boundedFlatCoefficientSupportedSectionEquivalence

/-- Actual acyclic evaluation is the original supported evaluation followed by conversion. -/
theorem boundedFlatCoefficientSupportAcyclicEvaluationKEquiv_eq (a : Under R) (n : ℕ) :
    boundedFlatCoefficientEvaluationKEquiv
        (boundedFlatCoefficientSupportedSectionWaldhausen (schemeMap f a))
        (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a)))
        (boundedFlatCoefficientSupportAcyclicEquivalence f a)
        (boundedFlatCoefficientSupportAcyclicEvaluation_exact f a)
        (boundedFlatCoefficientSupportAcyclicEquivalence_inverse_exact f a) n =
      (boundedFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n).trans
        (boundedFlatPerfectAcyclicSupportedKEquiv (schemeMap f a) n).symm := by
  ext x
  change boundedFlatCoefficientEvaluationKEquiv _ _ _ _ _ n x =
    KMap (boundedFlatPerfectSupportedToAcyclic_exact (schemeMap f a)) n
      (boundedFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n x)
  simpa only [KMap_id, MonoidHom.id_apply, boundedFlatCoefficientSupportedSectionKEquiv] using
    boundedFlatCoefficientEvaluationKEquiv_natural
      (boundedFlatCoefficientSupportedSectionWaldhausen (schemeMap f a))
      (boundedFlatPerfectSupportedWaldhausen (schemeMap f a))
      (boundedFlatCoefficientSupportedSectionEquivalence (schemeMap f a))
      (boundedFlatCoefficientSupportedSectionEquivalence_functor_exact (schemeMap f a))
      (boundedFlatCoefficientSupportedSectionEquivalence_inverse_exact (schemeMap f a))
      (boundedFlatCoefficientSupportedSectionWaldhausen (schemeMap f a))
      (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a)))
      (boundedFlatCoefficientSupportAcyclicEquivalence f a)
      (boundedFlatCoefficientSupportAcyclicEvaluation_exact f a)
      (boundedFlatCoefficientSupportAcyclicEquivalence_inverse_exact f a)
      (IsExact.id _ _)
      (boundedFlatPerfectSupportedToAcyclic_exact (schemeMap f a))
      (by
        change 𝟭 _ ⋙ boundedFlatCoefficientSupportAcyclicEvaluation f a ≅
          (boundedFlatCoefficientSupportedSectionEquivalence (schemeMap f a)).functor ⋙
            boundedFlatPerfectSupportedToAcyclic (schemeMap f a)
        rw [Functor.id_comp, boundedFlatCoefficientSupportedSectionEquivalence_functor]
        exact Iso.refl _) n x

/-- Inverse actual acyclic evaluation uses exactly the original two inverse comparisons. -/
theorem boundedFlatCoefficientSupportAcyclicEvaluationKEquiv_symm_apply (a : Under R) (n : ℕ)
    (y : (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))).K n) :
    (boundedFlatCoefficientEvaluationKEquiv
        (boundedFlatCoefficientSupportedSectionWaldhausen (schemeMap f a))
        (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a)))
        (boundedFlatCoefficientSupportAcyclicEquivalence f a)
        (boundedFlatCoefficientSupportAcyclicEvaluation_exact f a)
        (boundedFlatCoefficientSupportAcyclicEquivalence_inverse_exact f a) n).symm y =
      (boundedFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n).symm
        (boundedFlatPerfectAcyclicSupportedKEquiv (schemeMap f a) n y) := by
  rw [boundedFlatCoefficientSupportAcyclicEvaluationKEquiv_eq]
  rfl

/-- The original geometric boundary becomes the existing supported bounded-flat boundary. -/
theorem boundedFlatCoefficientSupportAcyclicEvaluationKEquiv_symm_connecting
    (a : Under R) (n : ℕ) (x : BoundedFlatPerfectOpenK (schemeMap f a) (n + 1)) :
    (boundedFlatCoefficientEvaluationKEquiv
        (boundedFlatCoefficientSupportedSectionWaldhausen (schemeMap f a))
        (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a)))
        (boundedFlatCoefficientSupportAcyclicEquivalence f a)
        (boundedFlatCoefficientSupportAcyclicEvaluation_exact f a)
        (boundedFlatCoefficientSupportAcyclicEquivalence_inverse_exact f a) n).symm
      (changeWeakConnectingHom (boundedFlatPerfectOpenNested (schemeMap f a))
        (boundedFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence (schemeMap f a)) n x) =
      (boundedFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n).symm
        (boundedFlatPerfectOpenConnectingHom (schemeMap f a) n x) := by
  rw [boundedFlatCoefficientSupportAcyclicEvaluationKEquiv_symm_apply]
  rfl

end Quillen.PerfectComplexes
