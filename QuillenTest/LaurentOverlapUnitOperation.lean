/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LaurentOverlapUnitOperation

/-! Literal original overlap equivalence, all input degrees and the exact inverse-unit sign. -/
public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.LaurentOverlapUnitOperation

/-- The complete original operation homomorphism retains the inverse overlap map. -/
theorem original_homomorphism (R : CommRingCat.{u}) (n : ℕ) :
    (laurentOverlapEquiv R (n + 1)).symm.toMonoidHom.comp
        (originalKSelfTrackOperation (perfectWaldhausen (Spec (.of (Polynomial R))))
          (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
          (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n) =
      originalKSelfTrackOperation (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (overlapOpen R).toScheme)
        (perfectFlatUnitHomotopy (overlapOpen R).ι (overlapLaurentGlobalUnit R)) n :=
  laurentOverlapEquiv_comp_unitSelfTrack R n

/-- Every original polynomial coefficient class is allowed, with no chosen representative. -/
theorem original_input (R : CommRingCat.{u}) (n : ℕ)
    (a : PerfectK (Spec (.of (Polynomial R))) n) :
    (laurentOverlapEquiv R (n + 1)).symm
        (originalKSelfTrackOperation (perfectWaldhausen (Spec (.of (Polynomial R))))
          (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
          (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n a) =
      originalKSelfTrackOperation (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (overlapOpen R).toScheme)
        (perfectFlatUnitHomotopy (overlapOpen R).ι (overlapLaurentGlobalUnit R)) n a :=
  laurentOverlapEquiv_unitSelfTrack R n a

/-- Arbitrary degree-zero input uses the same whole-track comparison. -/
theorem original_k_zero (R : CommRingCat.{u})
    (a : PerfectK (Spec (.of (Polynomial R))) 0) :
    (laurentOverlapEquiv R 1).symm
        (originalKSelfTrackOperation (perfectWaldhausen (Spec (.of (Polynomial R))))
          (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
          (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) 0 a) =
      originalKSelfTrackOperation (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (overlapOpen R).toScheme)
        (perfectFlatUnitHomotopy (overlapOpen R).ι (overlapLaurentGlobalUnit R)) 0 a :=
  laurentOverlapEquiv_unitSelfTrack R 0 a

/-- The negative-chart scalar's inverse unit contributes exactly one output inverse. -/
theorem original_inverse_unit (R : CommRingCat.{u}) (n : ℕ)
    (a : PerfectK (Spec (.of (Polynomial R))) n) :
    (laurentOverlapEquiv R (n + 1)).symm
        (originalKSelfTrackOperation (perfectWaldhausen (Spec (.of (Polynomial R))))
          (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
          (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n a) =
      (originalKSelfTrackOperation (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (overlapOpen R).toScheme)
        (perfectFlatUnitHomotopy (overlapOpen R).ι (overlapLaurentGlobalUnit R)⁻¹) n a)⁻¹ :=
  laurentOverlapEquiv_unitSelfTrack_inverse R n a

end QuillenTest.LaurentOverlapUnitOperation
