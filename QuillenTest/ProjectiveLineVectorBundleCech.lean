/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.VectorBundleCech
public import Mathlib.Data.ZMod.Basic

/-! # Original geometric vector-bundle Cech models

These consumers retain the actual sheaf difference, both scalar structures, the
cochain degree convention, and both homotopies over arbitrary commutative rings.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModuleCat HomologicalComplex
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine Quillen.ModuleComplex
open AlgebraicGeometry.Scheme.PolynomialLaurent Quillen.LaurentProjector
universe u
namespace QuillenTest.ProjectiveLineVectorBundleCech

open Quillen
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)

/-- The test names the literal pushforward of the original sheaf difference. -/
abbrev originalDifference :=
  moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (projection R)).map
    (TwoOpen.sheafDifference (laurentPlus R) (laurentMinus R)
      (plusChart R) (minusChart R) (overlap_equation R) M))

/-- The actual geometric signed square retains the original differential. -/
theorem signed_square :
    originalDifference R M ≫ (overlapLocalizedSectionsIso R M).hom =
      (originalCechSourceIso R M).hom ≫ ofHom (chartSectionDifference R M) :=
  original_sheafDifference_sections R M

/-- The coordinate source retains the original categorical first projection. -/
theorem source_first_projection :
    (originalCechSourceIso R M).hom ≫ ofHom (LinearMap.fst R _ _) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (projection R)).map
        (prod.fst : (openLocalization (plusChart R)).obj M ⨯
          (openLocalization (minusChart R)).obj M ⟶ _)) ≫
        (plusLocalizedSectionsIso R M).hom :=
  originalCechSourceIso_hom_fst R M

/-- The actual overlap transports the signed adjunction-unit differential. -/
theorem signed_unit_coordinates [M.IsQuasicoherent] :
    (chartOverlapSectionsIso R M).hom.hom.comp
        (moduleDifference (plusChartModule R M) (minusChartModule R M)
          (chartModuleOverlapIso R M)) = chartSectionDifference R M :=
  chartSectionDifference_coordinates R M

/-- The source comparison also retains the original second projection. -/
theorem source_second_projection :
    (originalCechSourceIso R M).hom ≫ ofHom (LinearMap.snd R _ _) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (projection R)).map
        (prod.snd : (openLocalization (plusChart R)).obj M ⨯
          (openLocalization (minusChart R)).obj M ⟶ _)) ≫
        (minusLocalizedSectionsIso R M).hom :=
  originalCechSourceIso_hom_snd R M

/-- The actual degree-zero-to-one arrow has the original sign. -/
theorem original_degrees :
    (linearMapCechSourceIso (originalDifference R M).hom).hom ≫
        (linearMapCechComplex (originalDifference R M).hom).d 0 1 =
      originalDifference R M ≫
        (linearMapCechTargetIso (originalDifference R M).hom).hom :=
  linearMapCechSource_d _

/-- Both chain homotopies apply to the actual original geometric complex. -/
theorem original_chain_maps [IsFiniteLocallyFree (twoChartLine R) M] :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ k, k ≠ 0 → k ≠ 1 → IsZero (P.X k)) ∧
      (∀ k, Module.Finite R (P.X k) ∧ Module.Projective R (P.X k)) ∧
      ∃ f : linearMapCechComplex (originalDifference R M).hom ⟶ P,
      ∃ g : P ⟶ linearMapCechComplex (originalDifference R M).hom,
      Nonempty (Homotopy (f ≫ g) (𝟙 _)) ∧ Nonempty (Homotopy (g ≫ f) (𝟙 _)) := by
  obtain ⟨P, hP, hfin, ⟨h⟩⟩ := exists_original_vectorBundle_cech_model R M
  exact ⟨P, hP, hfin, h.hom, h.inv, ⟨h.homotopyHomInvId⟩, ⟨h.homotopyInvHomId⟩⟩

/-- The nonreduced base case retains arbitrary finite locally free sheaves. -/
theorem nonreduced_model (M : (twoChartLine (.of (ZMod 4))).Modules)
    [IsFiniteLocallyFree (twoChartLine (.of (ZMod 4))) M] :
    ∃ P : CochainComplex (ModuleCat (ZMod 4)) ℤ,
      (∀ k, k ≠ 0 → k ≠ 1 → IsZero (P.X k)) ∧
      (∀ k, Module.Finite (ZMod 4) (P.X k) ∧ Module.Projective (ZMod 4) (P.X k)) ∧
      Nonempty (HomotopyEquiv
        (linearMapCechComplex (originalDifference (.of (ZMod 4)) M).hom) P) :=
  exists_original_vectorBundle_cech_model _ M

/-- The same theorem includes the zero ring without a nontriviality premise. -/
theorem zero_ring_model (M : (twoChartLine (.of (ZMod 1))).Modules)
    [IsFiniteLocallyFree (twoChartLine (.of (ZMod 1))) M] :
    ∃ P : CochainComplex (ModuleCat (ZMod 1)) ℤ,
      (∀ k, k ≠ 0 → k ≠ 1 → IsZero (P.X k)) ∧
      (∀ k, Module.Finite (ZMod 1) (P.X k) ∧ Module.Projective (ZMod 1) (P.X k)) ∧
      Nonempty (HomotopyEquiv
        (linearMapCechComplex (originalDifference (.of (ZMod 1)) M).hom) P) :=
  exists_original_vectorBundle_cech_model _ M

end QuillenTest.ProjectiveLineVectorBundleCech
