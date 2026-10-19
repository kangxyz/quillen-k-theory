/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientEvaluationKStable
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportEvaluationNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenCofinality

/-!
# The original K-classes of the support localization evaluation square

The three literal chosen-zero evaluation Model arrows preserve their original
coefficient K-equivalences. The supported map is invertible in every nonnegative
degree by the actual evaluation equivalence, without a compactness hypothesis.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatCoefficientSupportedEvaluation boundedFlatCoefficientSupportedSectionEquivalence
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The literal coarse evaluation retains the existing relative-open K-equivalence. -/
theorem coarseOriginalEvaluationModelMap_stable (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientOpenModel f a).waldhausen.K n) :
    (stableHomotopyFunctor (n : ℤ)).map (prespectrumMap (coarseOriginalEvaluationModelMap f a))
        (modelKStableEquiv (boundedFlatCoefficientOpenModel f a) n (Additive.ofMul x)) =
      originalKStableEquiv (boundedFlatPerfectOpenWaldhausen (schemeMap f a)) n
        (Additive.ofMul (boundedFlatCoefficientOpenKEquiv f a n x)) := by
  have h := boundedFlatCoefficientEvaluationKEquiv_stable
    (boundedFlatCoefficientOpenModel f a)
    (boundedFlatPerfectOpenWaldhausen (schemeMap f a))
    (boundedFlatCoefficientSectionEquivalence (op Q, a))
    (boundedFlatCoefficientOpenEvaluation_coarse_exact f a)
    (boundedFlatCoefficientOpenEquivalence_inverse_exact f a)
    (coarseOriginalEvaluationModelMap f a) rfl n x
  exact h

/-- The actual ambient evaluation preserves the original bounded-flat K-class. -/
theorem ambientOriginalEvaluationModelMap_stable (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSectionModel (op Q, a)).waldhausen.K n) :
    (stableHomotopyFunctor (n : ℤ)).map (prespectrumMap (ambientOriginalEvaluationModelMap a))
        (modelKStableEquiv (boundedFlatCoefficientSectionModel (op Q, a)) n (Additive.ofMul x)) =
      originalKStableEquiv (boundedFlatPerfectWaldhausen (space (op Q, a))) n
        (Additive.ofMul (boundedFlatCoefficientSectionKEquiv (op Q, a) n x)) := by
  have h := boundedFlatCoefficientEvaluationKEquiv_stable
    (boundedFlatCoefficientSectionModel (op Q, a))
    (boundedFlatPerfectWaldhausen (space (op Q, a)))
    (boundedFlatCoefficientSectionEquivalence (op Q, a))
    (boundedFlatCoefficientOriginalEvaluation_exact (op Q, a))
    (boundedFlatCoefficientSectionEquivalence_inverse_exact (op Q, a))
    (ambientOriginalEvaluationModelMap a) rfl n x
  exact h

/-- Original support evaluation and acyclic conversion retain the original stable representative. -/
theorem supportAcyclicEvaluationModelMap_stable (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedModel f a).waldhausen.K n) :
    (stableHomotopyFunctor (n : ℤ)).map (prespectrumMap (supportAcyclicEvaluationModelMap f a))
        (modelKStableEquiv (boundedFlatCoefficientSupportedModel f a) n (Additive.ofMul x)) =
      originalKStableEquiv (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))) n
        (Additive.ofMul (boundedFlatCoefficientEvaluationKEquiv
          (boundedFlatCoefficientSupportedModel f a).waldhausen
          (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a)))
          (boundedFlatCoefficientSupportAcyclicEquivalence f a)
          (boundedFlatCoefficientSupportAcyclicEvaluation_exact f a)
          (boundedFlatCoefficientSupportAcyclicEquivalence_inverse_exact f a) n x)) := by
  have h := boundedFlatCoefficientEvaluationKEquiv_stable
    (boundedFlatCoefficientSupportedModel f a)
    (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a)))
    (boundedFlatCoefficientSupportAcyclicEquivalence f a)
    (boundedFlatCoefficientSupportAcyclicEvaluation_exact f a)
    (boundedFlatCoefficientSupportAcyclicEquivalence_inverse_exact f a)
    (supportAcyclicEvaluationModelMap f a) rfl n x
  exact h

/-- The same actual support evaluation is invertible in every nonnegative stable degree. -/
theorem supportAcyclicEvaluationModelMap_stable_isIso (a : Under R) (n : ℕ) :
    IsIso ((stableHomotopyFunctor (n : ℤ)).map
      (prespectrumMap (supportAcyclicEvaluationModelMap f a))) :=
  boundedFlatCoefficientEvaluationKEquiv_stable_isIso _ _
    (boundedFlatCoefficientSupportAcyclicEquivalence f a)
    (boundedFlatCoefficientSupportAcyclicEvaluation_exact f a)
    (boundedFlatCoefficientSupportAcyclicEquivalence_inverse_exact f a)
    (supportAcyclicEvaluationModelMap f a) rfl n

end Quillen.PerfectComplexes
