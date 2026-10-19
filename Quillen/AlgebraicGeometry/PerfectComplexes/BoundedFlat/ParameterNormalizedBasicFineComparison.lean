/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedBasicCurrentBoundary
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterFineConnectingComparison

/-!
# The actual basic normalized row and the original fine boundary

The comparison is the original current-to-fine comparison after the inverse of
the actual current-to-normalized map. Its boundary square follows from the two
proved whole-null squares, in every signed degree. The basic connecting map is
the independently constructed path-space boundary.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace Quillen.PerfectComplexes.ParameterNormalizedBasicLocalization
attribute [local instance] basicOver_compactSpace basicOver_quasiSeparatedSpace
open GlobalSectionChangeIndex ParameterLaurentTrack ParameterFullCurrentNull

private theorem comparison_triangle {C : Type*} [Category C]
    {A B D : C} (s : A ⟶ B) [IsIso s] (v : A ≅ D) :
    s ≫ ((asIso s).symm ≪≫ v).hom = v.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, ← Category.assoc,
    IsIso.hom_inv_id, Category.id_comp]

/-- The original supported fine object is compared by the actual normalized map. -/
def normalizedFineSupportComparison
    {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup
      (ParameterTensorNormalizedRowPresentation.supported f.left (specUnder.obj a)) d ≅
    stableHomotopyGroup ((boundedFlatCoefficientSupportedBassTelescopeFunctor f).obj a) d := by
  have : IsIso ((stableHomotopyFunctor d).map
      (ParameterTensorNormalizedRowPresentation.supportedComparison f.left (specUnder.obj a))) :=
    ParameterTensorNormalizedRowPresentation.supportedComparison_stable f.left (specUnder.obj a) d
  exact (asIso ((stableHomotopyFunctor d).map
    (ParameterTensorNormalizedRowPresentation.supportedComparison f.left
      (specUnder.obj a)))).symm ≪≫
      currentFineSupportComparison f a d

/-- The supported comparison retains the original current comparison as a literal triangle. -/
@[reassoc]
theorem normalizedFineSupportComparison_triangle
    {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    (stableHomotopyFunctor d).map
        (ParameterTensorNormalizedRowPresentation.supportedComparison f.left (specUnder.obj a)) ≫
      (normalizedFineSupportComparison f a d).hom = (currentFineSupportComparison f a d).hom := by
  have : IsIso ((stableHomotopyFunctor d).map
      (ParameterTensorNormalizedRowPresentation.supportedComparison f.left (specUnder.obj a))) :=
    ParameterTensorNormalizedRowPresentation.supportedComparison_stable f.left (specUnder.obj a) d
  exact comparison_triangle _ _

/-- The original ambient comparison applies to both middle and open objects of the basic row. -/
def normalizedFineAmbientComparison
    (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup
      (ParameterTensorNormalizedRowPresentation.ambient P.left (specUnder.obj a)) d ≅
    stableHomotopyGroup ((boundedFlatCoefficientAmbientBassTelescopeFunctor P).obj a) d := by
  have : IsIso ((stableHomotopyFunctor d).map
      (ParameterTensorNormalizedRowPresentation.ambientComparison P.left (specUnder.obj a))) :=
    ParameterTensorNormalizedRowPresentation.ambientComparison_stable P.left (specUnder.obj a) d
  exact (asIso ((stableHomotopyFunctor d).map
    (ParameterTensorNormalizedRowPresentation.ambientComparison P.left (specUnder.obj a)))).symm ≪≫
      currentFineOpenComparison (𝟙 P) a d

/-- The ambient comparison retains the original open comparison for any original restriction. -/
@[reassoc]
theorem normalizedFineAmbientComparison_triangle
    {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    (stableHomotopyFunctor d).map
        (ParameterTensorNormalizedRowPresentation.ambientComparison P.left (specUnder.obj a)) ≫
      (normalizedFineAmbientComparison P a d).hom = (currentFineOpenComparison f a d).hom := by
  have : IsIso ((stableHomotopyFunctor d).map
      (ParameterTensorNormalizedRowPresentation.ambientComparison P.left (specUnder.obj a))) :=
    ParameterTensorNormalizedRowPresentation.ambientComparison_stable P.left (specUnder.obj a) d
  exact comparison_triangle _ _

private theorem boundary_triangle {C : Type*} [Category C]
    {A B D A' B' D' : C} (s : A ⟶ B) (t : A' ⟶ B')
    (e : B ⟶ D) (e' : B' ⟶ D') (v : A ⟶ D) (v' : A' ⟶ D')
    (δ : A ⟶ A') (δ' : B ⟶ B') (δ'' : D ⟶ D')
    (hs : s ≫ e = v) (ht : t ≫ e' = v')
    (hr : δ ≫ t = s ≫ δ') (hf : δ ≫ v' = v ≫ δ'') (hiso : IsIso s) :
    δ' ≫ e' = e ≫ δ'' := by
  have : IsIso s := hiso
  apply (cancel_epi s).1
  rw [← Category.assoc, ← hr, Category.assoc, ht, hf, ← hs, Category.assoc]

/-- The independently defined basic boundary preserves the original fine boundary in all degrees. -/
@[reassoc]
theorem basicSpecConnecting_fine (Q : Scheme.{u}) (U : Q.Opens)
    [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U]
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    let f := basicOverInclusion Q U;
    basicSpecConnecting Q U a d ≫ (normalizedFineSupportComparison f a d).hom =
      (normalizedFineAmbientComparison (Over.mk (toIntegerBase U.toScheme)) a (d + 1)).hom ≫
        boundedFlatCoefficientFineLocalizationConnecting f a d := by
  let f := basicOverInclusion Q U
  exact boundary_triangle _ _ _ _ _ _ _ _ _
    (normalizedFineAmbientComparison_triangle f a (d + 1))
    (normalizedFineSupportComparison_triangle f a d)
    (current_basic_normalized_connecting Q U a d) (current_fine_connecting f a d)
    (ParameterTensorNormalizedRowPresentation.ambientComparison_stable
      (Over.mk (toIntegerBase U.toScheme)).left (specUnder.obj a) (d + 1))

end Quillen.PerfectComplexes.ParameterNormalizedBasicLocalization
