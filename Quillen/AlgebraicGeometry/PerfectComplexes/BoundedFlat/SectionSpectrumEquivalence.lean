/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionComparison
public import Quillen.Waldhausen.SConstruction.Iterated.ExactModelEquivalence

/-!
# The original evaluation comparison is an actual prespectrum equivalence

The genuine exact evaluation equivalence, with original universe lifting, has a canonically
normalized actual inverse. Its original unit and counit produce full coherent prespectrum
homotopies. Thus the unchanged comparison is a homotopy equivalence at every level, including
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

/-- The actual normalized inverse of original evaluation at the prespectrum level. -/
def boundedFlatAffineSectionEvaluationInversePrespectrumMap (R : CommRingCat.{u}) :
    originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R)) ⟶
      boundedFlatAffineSectionPrespectrumFunctor.obj R :=
  prespectrumMap (ExactModelEquivalence.backward
    (V := boundedFlatAffineSectionModel R)
    (W := modelOf (boundedFlatPerfectWaldhausen (Spec R)))
    (boundedFlatAffineSectionSmallEquivalence R)
    (boundedFlatAffineSectionSmallEquivalence_inverse_exact R))

/-- The whole left inverse homotopy of the unchanged original evaluation map. -/
def boundedFlatAffineSectionEvaluationLeftHomotopy (R : CommRingCat.{u}) :
    LoopPrespectrum.Homotopy
      (boundedFlatAffineSectionEvaluationPrespectrumMap R ≫
        boundedFlatAffineSectionEvaluationInversePrespectrumMap R)
      (𝟙 (boundedFlatAffineSectionPrespectrumFunctor.obj R)) :=
  ExactModelEquivalence.leftHomotopy
    (V := boundedFlatAffineSectionModel R)
    (W := modelOf (boundedFlatPerfectWaldhausen (Spec R)))
    (boundedFlatAffineSectionSmallEquivalence R)
    (boundedFlatAffineSectionSmallEquivalence_exact R)
    (boundedFlatAffineSectionSmallEquivalence_inverse_exact R)
    (boundedFlatAffineSectionEvaluationModelMap R).zero

/-- The whole right inverse homotopy of the unchanged original evaluation map. -/
def boundedFlatAffineSectionEvaluationRightHomotopy (R : CommRingCat.{u}) :
    LoopPrespectrum.Homotopy
      (boundedFlatAffineSectionEvaluationInversePrespectrumMap R ≫
        boundedFlatAffineSectionEvaluationPrespectrumMap R)
      (𝟙 (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R)))) :=
  ExactModelEquivalence.rightHomotopy
    (V := boundedFlatAffineSectionModel R)
    (W := modelOf (boundedFlatPerfectWaldhausen (Spec R)))
    (boundedFlatAffineSectionSmallEquivalence R)
    (boundedFlatAffineSectionSmallEquivalence_exact R)
    (boundedFlatAffineSectionSmallEquivalence_inverse_exact R)
    (boundedFlatAffineSectionEvaluationModelMap R).zero

/-- The actual original comparison has its proved homotopy inverse at every level. -/
def boundedFlatAffineSectionEvaluationLevelHomotopyEquiv (R : CommRingCat.{u}) (n : ℕ) :
    ContinuousMap.HomotopyEquiv
      ((boundedFlatAffineSectionPrespectrumFunctor.obj R).space n)
      ((originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :=
  ExactModelEquivalence.levelHomotopyEquiv
    (V := boundedFlatAffineSectionModel R)
    (W := modelOf (boundedFlatPerfectWaldhausen (Spec R)))
    (boundedFlatAffineSectionSmallEquivalence R)
    (boundedFlatAffineSectionSmallEquivalence_exact R)
    (boundedFlatAffineSectionSmallEquivalence_inverse_exact R)
    (boundedFlatAffineSectionEvaluationModelMap R).zero n

/-- The unchanged original comparison is a complete weak equivalence on every level. -/
theorem boundedFlatAffineSectionEvaluation_level_isWeakHomotopyEquivalence
    (R : CommRingCat.{u}) (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedFlatAffineSectionEvaluationPrespectrumMap R).map n) :=
  ExactModelEquivalence.level_isWeakHomotopyEquivalence
    (V := boundedFlatAffineSectionModel R)
    (W := modelOf (boundedFlatPerfectWaldhausen (Spec R)))
    (boundedFlatAffineSectionSmallEquivalence R)
    (boundedFlatAffineSectionSmallEquivalence_exact R)
    (boundedFlatAffineSectionSmallEquivalence_inverse_exact R)
    (boundedFlatAffineSectionEvaluationModelMap R).zero n

/-- Hence the same original evaluation map is a genuine stable equivalence. -/
theorem boundedFlatAffineSectionEvaluation_isStableEquivalence (R : CommRingCat.{u}) :
    LoopPrespectrum.IsStableEquivalence (boundedFlatAffineSectionEvaluationPrespectrumMap R) :=
  ExactModelEquivalence.isStableEquivalence
    (V := boundedFlatAffineSectionModel R)
    (W := modelOf (boundedFlatPerfectWaldhausen (Spec R)))
    (boundedFlatAffineSectionSmallEquivalence R)
    (boundedFlatAffineSectionSmallEquivalence_exact R)
    (boundedFlatAffineSectionSmallEquivalence_inverse_exact R)
    (boundedFlatAffineSectionEvaluationModelMap R).zero

end Quillen.PerfectComplexes
