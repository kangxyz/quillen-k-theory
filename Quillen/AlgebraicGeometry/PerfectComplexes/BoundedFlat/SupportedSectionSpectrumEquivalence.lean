/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionComparison
public import Quillen.Waldhausen.SConstruction.Iterated.ExactModelEquivalence

/-!
# Canonically normalized supported evaluation is an actual prespectrum equivalence

The genuine supported evaluation equivalence, with original universe lifting and its specified
chosen-zero normalization, has a canonically normalized actual inverse. The transported original
unit and counit produce full coherent prespectrum homotopies. Thus this normalized map is a
homotopy equivalence at every level, including
level zero, and a stable equivalence. Coefficient and Bass-seed coherence remain separate.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}}

/-- The actual normalized inverse of original evaluation at the prespectrum level. -/
def boundedFlatAffineSupportedSectionEvaluationInversePrespectrumMap
    (j : U ⟶ Spec R) [IsOpenImmersion j] :
    originalPrespectrum (boundedFlatPerfectSupportedWaldhausen j) ⟶
      prespectrum (boundedFlatAffineSupportedSectionModel j) :=
  prespectrumMap (ExactModelEquivalence.backward
    (V := boundedFlatAffineSupportedSectionModel j)
    (W := modelOf (boundedFlatPerfectSupportedWaldhausen j))
    (boundedFlatAffineSupportedSectionNormalizedEquivalence j)
    (boundedFlatAffineSupportedSectionNormalizedEquivalence_inverse_exact j))

/-- The whole left inverse homotopy of the specified normalized evaluation map. -/
def boundedFlatAffineSupportedSectionEvaluationLeftHomotopy
    (j : U ⟶ Spec R) [IsOpenImmersion j] :
    LoopPrespectrum.Homotopy
      (boundedFlatAffineSupportedSectionEvaluationPrespectrumMap j ≫
        boundedFlatAffineSupportedSectionEvaluationInversePrespectrumMap j)
      (𝟙 (prespectrum (boundedFlatAffineSupportedSectionModel j))) :=
  ExactModelEquivalence.leftHomotopy
    (V := boundedFlatAffineSupportedSectionModel j)
    (W := modelOf (boundedFlatPerfectSupportedWaldhausen j))
    (boundedFlatAffineSupportedSectionNormalizedEquivalence j)
    (boundedFlatAffineSupportedSectionNormalizedEquivalence_exact j)
    (boundedFlatAffineSupportedSectionNormalizedEquivalence_inverse_exact j)
    (boundedFlatAffineSupportedSectionEvaluationModelMap j).zero

/-- The whole right inverse homotopy of the specified normalized evaluation map. -/
def boundedFlatAffineSupportedSectionEvaluationRightHomotopy
    (j : U ⟶ Spec R) [IsOpenImmersion j] :
    LoopPrespectrum.Homotopy
      (boundedFlatAffineSupportedSectionEvaluationInversePrespectrumMap j ≫
        boundedFlatAffineSupportedSectionEvaluationPrespectrumMap j)
      (𝟙 (originalPrespectrum (boundedFlatPerfectSupportedWaldhausen j))) :=
  ExactModelEquivalence.rightHomotopy
    (V := boundedFlatAffineSupportedSectionModel j)
    (W := modelOf (boundedFlatPerfectSupportedWaldhausen j))
    (boundedFlatAffineSupportedSectionNormalizedEquivalence j)
    (boundedFlatAffineSupportedSectionNormalizedEquivalence_exact j)
    (boundedFlatAffineSupportedSectionNormalizedEquivalence_inverse_exact j)
    (boundedFlatAffineSupportedSectionEvaluationModelMap j).zero

/-- The actual original comparison has its proved homotopy inverse at every level. -/
def boundedFlatAffineSupportedSectionEvaluationLevelHomotopyEquiv
    (j : U ⟶ Spec R) [IsOpenImmersion j] (n : ℕ) :
    ContinuousMap.HomotopyEquiv
      ((prespectrum (boundedFlatAffineSupportedSectionModel j)).space n)
      ((originalPrespectrum (boundedFlatPerfectSupportedWaldhausen j)).space n) :=
  ExactModelEquivalence.levelHomotopyEquiv
    (V := boundedFlatAffineSupportedSectionModel j)
    (W := modelOf (boundedFlatPerfectSupportedWaldhausen j))
    (boundedFlatAffineSupportedSectionNormalizedEquivalence j)
    (boundedFlatAffineSupportedSectionNormalizedEquivalence_exact j)
    (boundedFlatAffineSupportedSectionNormalizedEquivalence_inverse_exact j)
    (boundedFlatAffineSupportedSectionEvaluationModelMap j).zero n

/-- The specified normalized comparison is a complete weak equivalence on every level. -/
theorem boundedFlatAffineSupportedSectionEvaluation_level_isWeakHomotopyEquivalence
    (j : U ⟶ Spec R) [IsOpenImmersion j] (n : ℕ) :
    IsWeakHomotopyEquivalence
      ((boundedFlatAffineSupportedSectionEvaluationPrespectrumMap j).map n) :=
  ExactModelEquivalence.level_isWeakHomotopyEquivalence
    (V := boundedFlatAffineSupportedSectionModel j)
    (W := modelOf (boundedFlatPerfectSupportedWaldhausen j))
    (boundedFlatAffineSupportedSectionNormalizedEquivalence j)
    (boundedFlatAffineSupportedSectionNormalizedEquivalence_exact j)
    (boundedFlatAffineSupportedSectionNormalizedEquivalence_inverse_exact j)
    (boundedFlatAffineSupportedSectionEvaluationModelMap j).zero n

/-- Hence the same normalized evaluation map is a genuine stable equivalence. -/
theorem boundedFlatAffineSupportedSectionEvaluation_isStableEquivalence
    (j : U ⟶ Spec R) [IsOpenImmersion j] :
    LoopPrespectrum.IsStableEquivalence
      (boundedFlatAffineSupportedSectionEvaluationPrespectrumMap j) :=
  ExactModelEquivalence.isStableEquivalence
    (V := boundedFlatAffineSupportedSectionModel j)
    (W := modelOf (boundedFlatPerfectSupportedWaldhausen j))
    (boundedFlatAffineSupportedSectionNormalizedEquivalence j)
    (boundedFlatAffineSupportedSectionNormalizedEquivalence_exact j)
    (boundedFlatAffineSupportedSectionNormalizedEquivalence_inverse_exact j)
    (boundedFlatAffineSupportedSectionEvaluationModelMap j).zero

end Quillen.PerfectComplexes
