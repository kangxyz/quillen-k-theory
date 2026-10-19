/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportAcyclicKComparison

/-!
Original supported section evaluation identifies the unchanged geometric
relative-open boundary, without compactness assumptions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.Fibration
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u

namespace Consumer.CoefficientSupportAcyclicKComparison
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- Inverse coefficient evaluation detects vanishing of the actual supported boundary. -/
theorem inverse_acyclic_boundary_eq_one_iff (a : Under R) (n : ℕ)
    (x : BoundedFlatPerfectOpenK (schemeMap f a) (n + 1)) :
    (boundedFlatCoefficientEvaluationKEquiv
        (boundedFlatCoefficientSupportedSectionWaldhausen (schemeMap f a))
        (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a)))
        (boundedFlatCoefficientSupportAcyclicEquivalence f a)
        (boundedFlatCoefficientSupportAcyclicEvaluation_exact f a)
        (boundedFlatCoefficientSupportAcyclicEquivalence_inverse_exact f a) n).symm
      (changeWeakConnectingHom (boundedFlatPerfectOpenNested (schemeMap f a))
        (boundedFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence (schemeMap f a))
        n x) = 1 ↔
      boundedFlatPerfectOpenConnectingHom (schemeMap f a) n x = 1 := by
  rw [boundedFlatCoefficientSupportAcyclicEvaluationKEquiv_symm_connecting]
  exact (boundedFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n).symm.map_eq_one_iff

end Consumer.CoefficientSupportAcyclicKComparison
