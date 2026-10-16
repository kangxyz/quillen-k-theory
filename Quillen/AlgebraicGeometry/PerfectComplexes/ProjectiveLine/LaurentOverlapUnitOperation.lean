/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnitOpenComposition
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnitKOperation
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LaurentOverlapScalarBoundary

/-!
# Original Laurent overlap transport of unit operations in all connective degrees

The whole open/flat composition comparison transports the actual negative Laurent pullback
unit operation through the original inverse overlap equivalence. The inverse-unit consequence
retains the same geometric map and all original input classes, including degree zero.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.BassPositive

/-- Equality induction transports only the original flat map, with its unit fixed. -/
private theorem unitSelfTrack_map_eq {X Y : Scheme.{u}} (f g : X ⟶ Y)
    [Flat f] [Flat g] (hfg : f = g) (q : (Γ(X, ⊤))ˣ) (n : ℕ) :
    originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
        (perfectFlatUnitHomotopy f q) n =
      originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
        (perfectFlatUnitHomotopy g q) n := by
  subst g
  rfl

/-- The whole original overlap comparison preserves the actual forward unit operation. -/
theorem laurentOverlapEquiv_comp_unitSelfTrack (R : CommRingCat.{u}) (n : ℕ) :
    (laurentOverlapEquiv R (n + 1)).symm.toMonoidHom.comp
        (originalKSelfTrackOperation (perfectWaldhausen (Spec (.of (Polynomial R))))
          (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
          (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n) =
      originalKSelfTrackOperation (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (overlapOpen R).toScheme)
        (perfectFlatUnitHomotopy (overlapOpen R).ι (overlapLaurentGlobalUnit R)) n := by
  change (perfectKRestrict (overlapOpenIso R).inv (n + 1)).comp _ = _
  have h := perfectFlatUnitHomotopy_originalKOperation_restrict_comp
    (laurentMinus R) (overlapOpenIso R).inv (laurentGlobalUnit R) n
  have he := unitSelfTrack_map_eq
    ((overlapOpenIso R).inv ≫ laurentMinus R) (overlapOpen R).ι
    (overlapOpenIso_inv_laurentMinus R) (overlapLaurentGlobalUnit R) n
  exact h.trans he

/-- Every original polynomial-chart class retains the literal forward Laurent unit. -/
theorem laurentOverlapEquiv_unitSelfTrack (R : CommRingCat.{u}) (n : ℕ)
    (a : PerfectK (Spec (.of (Polynomial R))) n) :
    (laurentOverlapEquiv R (n + 1)).symm
        (originalKSelfTrackOperation (perfectWaldhausen (Spec (.of (Polynomial R))))
          (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
          (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n a) =
      originalKSelfTrackOperation (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (overlapOpen R).toScheme)
        (perfectFlatUnitHomotopy (overlapOpen R).ι (overlapLaurentGlobalUnit R)) n a :=
  DFunLike.congr_fun (laurentOverlapEquiv_comp_unitSelfTrack R n) a

/-- Only inversion of the original unit reverses the output; overlap transport is forward. -/
theorem laurentOverlapEquiv_unitSelfTrack_inverse (R : CommRingCat.{u}) (n : ℕ)
    (a : PerfectK (Spec (.of (Polynomial R))) n) :
    (laurentOverlapEquiv R (n + 1)).symm
        (originalKSelfTrackOperation (perfectWaldhausen (Spec (.of (Polynomial R))))
          (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
          (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n a) =
      (originalKSelfTrackOperation (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (overlapOpen R).toScheme)
        (perfectFlatUnitHomotopy (overlapOpen R).ι (overlapLaurentGlobalUnit R)⁻¹) n a)⁻¹ := by
  rw [laurentOverlapEquiv_unitSelfTrack,
    perfectFlatUnitHomotopy_originalKOperation_inv, inv_inv]

end Quillen.PerfectComplexes.ProjectiveLine.BassPositive
