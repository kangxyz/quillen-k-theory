/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterCurrentLowNegativeClasses
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterFineConnectingComparison

/-! # The original K₀-to-first-negative boundary in the current model

The independent current-stage intrinsic boundary agrees with the previously fixed
fine signed boundary under the original finite-bottom classes and literal current
inclusions. The actual integer-degree transport is retained. Only the separately
proved triviality of the zeroth and first finite words is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.PerfectComplexes.GlobalSectionChangeIndex SchemeNaturalSeed
universe u
namespace Quillen.PerfectComplexes.ParameterFullCurrentNull
open GlobalSectionChangeIndex
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

omit [CompactSpace Q.left] in
/-- The original open K₀ class is unchanged by the actual current-to-fine comparison. -/
@[reassoc]
theorem currentNegativeKComparison_zero_fine
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    letI : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
    (GlobalParameterCoefficient.currentNegativeKComparison P 0).hom.app a ≫
        (currentFineOpenComparison f a 0).hom =
      (boundedFlatCoefficientAmbientNegativeKTelescopeComparison P 0).hom.app a := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  exact GlobalParameterCoefficient.currentNegativeKComparison_low_fine P 0 (by omega) a

/-- The original first supported negative class is unchanged by the same actual comparison. -/
@[reassoc]
theorem currentNegativeKComparison_one_fine
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (GlobalSupportedParameterCoefficient.currentNegativeKComparison f 1).hom.app a ≫
        (currentFineSupportComparison f a (-1)).hom =
      (boundedFlatCoefficientSupportedNegativeKTelescopeComparison f 1).hom.app a := by
  exact GlobalSupportedParameterCoefficient.currentNegativeKComparison_low_fine f 1
    (by omega) a

/-- The original signed degree transport between the two low classes. -/
def firstNegativeClassBoundary {A B : AddCommGrpCat.{u + 1}}
    (O S : LoopPrespectrum.{u + 1})
    (x : A ⟶ (stableHomotopyFunctor 0).obj O)
    (δ : stableHomotopyGroup O (-1 + 1) ⟶ stableHomotopyGroup S (-1))
    (y : (stableHomotopyFunctor (-1)).obj S ⟶ B) : A ⟶ B :=
  x ≫ (negativeLocalizationDegreeIso 0).hom.app O ≫ δ ≫ y

private theorem low_boundary_square {C : Type*} [Category C]
    {A B D E F G : C} (x : A ⟶ B) (x' : A ⟶ D)
    (y : E ≅ F) (y' : E ≅ G) (g : B ⟶ D) (h : F ⟶ G)
    (δ : B ⟶ F) (δ' : D ⟶ G)
    (hx : x ≫ g = x') (hy : y.hom ≫ h = y'.hom) (hδ : δ ≫ h = g ≫ δ') :
    x ≫ δ ≫ y.inv = x' ≫ δ' ≫ y'.inv := by
  apply (cancel_mono y'.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hy, Iso.inv_hom_id_assoc, hδ, ← Category.assoc, hx]

private theorem first_class_boundary_square {A B : AddCommGrpCat.{u + 1}}
    (O S O' S' : LoopPrespectrum.{u + 1})
    (x : A ⟶ (stableHomotopyFunctor 0).obj O)
    (x' : A ⟶ (stableHomotopyFunctor 0).obj O')
    (y : B ≅ (stableHomotopyFunctor (-1)).obj S)
    (y' : B ≅ (stableHomotopyFunctor (-1)).obj S')
    (g : stableHomotopyGroup O 0 ≅ stableHomotopyGroup O' 0)
    (h : stableHomotopyGroup S (-1) ≅ stableHomotopyGroup S' (-1))
    (δ : stableHomotopyGroup O (-1 + 1) ⟶ stableHomotopyGroup S (-1))
    (δ' : stableHomotopyGroup O' (-1 + 1) ⟶ stableHomotopyGroup S' (-1))
    (hx : x ≫ g.hom = x') (hy : y.hom ≫ h.hom = y'.hom)
    (hδ : δ ≫ h.hom = g.hom ≫ δ') :
    firstNegativeClassBoundary O S x δ y.inv = firstNegativeClassBoundary O' S' x' δ' y'.inv := by
  change x ≫ 𝟙 _ ≫ δ ≫ y.inv = x' ≫ 𝟙 _ ≫ δ' ≫ y'.inv
  simpa only [Category.id_comp] using
    low_boundary_square x x' y y' g.hom h.hom δ δ' hx hy hδ

/-- The independent current intrinsic boundary through the unchanged original low classes. -/
def currentFirstNegativeConnecting
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (Bass.negativeKFunctor 0).obj ((boundedFlatCoefficientQuasiCompactRow P).obj a) ⟶
      (Bass.supportedNegativeKFunctor 1).obj
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  exact firstNegativeClassBoundary
    ((currentTelescope (ParameterLaurentTrack.ambientTrack P.left)).obj (specUnder.obj a))
    ((currentTelescope (ParameterLaurentTrack.supportedTrack f.left)).obj (specUnder.obj a))
    ((GlobalParameterCoefficient.currentNegativeKComparison P 0).hom.app a)
    (currentConnecting f a (-1))
    ((GlobalSupportedParameterCoefficient.currentNegativeKComparison f 1).inv.app a)

/-- The original K₀-to-N₁ signed boundary agrees without changing either original class. -/
theorem currentFirstNegativeConnecting_eq_original
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    currentFirstNegativeConnecting f a =
      boundedFlatCoefficientNegativeLocalizationConnecting f 0 a := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  have h := first_class_boundary_square _ _ _ _
    ((GlobalParameterCoefficient.currentNegativeKComparison P 0).hom.app a)
    ((boundedFlatCoefficientAmbientNegativeKTelescopeComparison P 0).hom.app a)
    ((GlobalSupportedParameterCoefficient.currentNegativeKComparison f 1).app a)
    ((boundedFlatCoefficientSupportedNegativeKTelescopeComparison f 1).app a)
    (currentFineOpenComparison f a 0) (currentFineSupportComparison f a (-1))
    (currentConnecting f a (-1)) (boundedFlatCoefficientFineLocalizationConnecting f a (-1))
    (currentNegativeKComparison_zero_fine f a) (currentNegativeKComparison_one_fine f a)
    (current_fine_connecting f a (-1))
  simp only [firstNegativeClassBoundary, currentFirstNegativeConnecting,
    boundedFlatCoefficientNegativeLocalizationConnecting,
    boundedFlatCoefficientFullOpenBassTelescopeFunctor_eq_ambient, Functor.comp_obj,
    Iso.app_inv] at h ⊢
  exact h

end Quillen.PerfectComplexes.ParameterFullCurrentNull
