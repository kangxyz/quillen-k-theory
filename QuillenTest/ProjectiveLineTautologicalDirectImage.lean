/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalDirectImage
public import Mathlib.Data.ZMod.Basic

/-! # Original tautological localization and relative cohomology consumers -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.TwoOpen
  AlgebraicGeometry.Scheme.ProjectiveLine
open Quillen.PolynomialBaseChange
universe u
namespace QuillenTest.ProjectiveLineTautologicalDirectImage

open Quillen

/-- The comparison retains the actual restricted global inclusion into the original unit square. -/
theorem original_localized_inclusion {R S : CommRingCat.{u}} (f : R ⟶ S)
    [IsOpenImmersion (Spec.map f)] :
    (tautologicalOpenIso f).hom ≫ tautologicalLineInclusion S =
      (Scheme.Modules.restrictFunctor (coefficientMap f)).map (tautologicalLineInclusion R) ≫
        (unitSquareRestrictionIso (coefficientMap f)).hom :=
  tautologicalOpenIso_inclusion f

/-- The positive chart comparison is built from the literal original restriction square. -/
theorem original_positive_chart {R S : CommRingCat.{u}} (f : R ⟶ S)
    [IsOpenImmersion (Spec.map f)] :
    (Scheme.Modules.restrictFunctor (plusChart S)).map (tautologicalOpenIso f).hom ≫
        (tautologicalLinePlusIso S).hom =
      (restrictionSquareIso (plusChart S) (coefficientMap f) (Spec.map (polynomialMap f))
          (plusChart R) (plusChart_coefficientMap f)).hom.app (tautologicalLine R) ≫
        (Scheme.Modules.restrictFunctor (Spec.map (polynomialMap f))).map
          (tautologicalLinePlusIso R).hom ≫
        (Scheme.Modules.restrictUnitIso (Spec.map (polynomialMap f))).hom :=
  tautologicalOpenIso_plus f

/-- The negative original trivialization is retained too. -/
theorem original_negative_chart {R S : CommRingCat.{u}} (f : R ⟶ S)
    [IsOpenImmersion (Spec.map f)] :
    (Scheme.Modules.restrictFunctor (minusChart S)).map (tautologicalOpenIso f).hom ≫
      (tautologicalLineMinusIso S).hom = (tautologicalOpenMinusIso f).hom :=
  tautologicalOpenIso_minus f

/-- Every actual section over the inverse image of any base open is zero. -/
theorem original_inverse_image_section_zero (R : CommRingCat.{u}) (U : (Spec R).Opens)
    (z : Γ(tautologicalLine R, (projection R) ⁻¹ᵁ U)) : z = 0 := by
  have h := (isZero_pushforward_projection_tautologicalLine R).eq_of_src (𝟙 _) 0
  exact congrArg (fun k => Scheme.Modules.Hom.app k U z) h

/-- A degree-one cocycle in the given resolution has an original principal-open section boundary. -/
theorem original_principal_cocycle_boundary (R : CommRingCat.{u}) (r : R)
    (I : InjectiveResolution (tautologicalLine R))
    (z : Γ(I.cocomplex.X 1, (projection R) ⁻¹ᵁ PrimeSpectrum.basicOpen r))
    (hz : Scheme.Modules.Hom.app (I.cocomplex.d 1 2)
      ((projection R) ⁻¹ᵁ PrimeSpectrum.basicOpen r) z = 0) :
    ∃ y : Γ(I.cocomplex.X 0, (projection R) ⁻¹ᵁ PrimeSpectrum.basicOpen r),
      Scheme.Modules.Hom.app (I.cocomplex.d 0 1)
        ((projection R) ⁻¹ᵁ PrimeSpectrum.basicOpen r) y = z := by
  have h := projection_tautological_resolution_on_open_exact (R := R)
    (CommRingCat.ofHom (algebraMap R (Localization.Away r))) I 1
  rw [Scheme.Hom.opensRange_localizationAway (R := R)] at h
  have h' := (HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)).mp h
  exact (ShortComplex.ab_exact_iff _).mp h' z hz

/-- Every degree targets the original right-derived module-sheaf direct image. -/
theorem original_all_degree_map (R : CommRingCat.{u}) (n : ℕ) (N : (Spec R).Modules)
    (f : ((Scheme.Modules.pushforward (projection R)).rightDerived n).obj
      (tautologicalLine R) ⟶ N) : f = 0 :=
  (isZero_rightDerived_projection_tautologicalLine R n).eq_of_src _ _

/-- Nonreduced bases satisfy the actual degree-zero direct-image vanishing. -/
theorem nonreduced_direct_image :
    IsZero ((Scheme.Modules.pushforward (projection (.of (ZMod 4)))).obj
      (tautologicalLine (.of (ZMod 4)))) := isZero_pushforward_projection_tautologicalLine _

/-- The zero ring is retained in all derived degrees. -/
theorem zero_ring_derived (n : ℕ) :
    IsZero (((Scheme.Modules.pushforward (projection (.of (ZMod 1)))).rightDerived n).obj
      (tautologicalLine (.of (ZMod 1)))) := isZero_rightDerived_projection_tautologicalLine _ n

end QuillenTest.ProjectiveLineTautologicalDirectImage
