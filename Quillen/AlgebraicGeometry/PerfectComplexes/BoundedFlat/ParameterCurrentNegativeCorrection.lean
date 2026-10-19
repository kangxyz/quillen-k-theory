/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterCurrentLowNegativeClasses
public import Quillen.KTheory.Bass.SchemeStageClassComparison

/-!
# The finite correction on the original negative classes

Conjugating the actual finite-stage word by the original finite-bottom class
comparison gives an automorphism of the original negative group. The specified
current-to-fine comparison carries the independent current class to the original
fine class preceded by this automorphism. No finite word is assumed trivial.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace Quillen.PerfectComplexes
open GlobalSectionChangeIndex SchemeNaturalSeed

namespace GlobalParameterCoefficient
variable (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
  [CompactSpace P.left] [QuasiSeparatedSpace P.left]

/-- The genuine finite-word correction, expressed on the unchanged original negative group. -/
def negativeClassCorrection (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (Bass.negativeKFunctor i).obj ((boundedFlatCoefficientQuasiCompactRow P).obj a) ≅
      (Bass.negativeKFunctor i).obj ((boundedFlatCoefficientQuasiCompactRow P).obj a) :=
  (finiteNegativeKComparison P i).app a ≪≫
    finiteStageStableIso (ParameterModels.ambient P.left) i (specUnder.obj a) (-(i : ℤ)) ≪≫
      ((finiteNegativeKComparison P i).app a).symm

/-- The original current class retains its finite correction through the fine comparison. -/
@[reassoc]
theorem currentNegativeKComparison_fine_correction (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (currentNegativeKComparison P i).hom.app a ≫
        (currentIteratedStableIso (ParameterModels.ambient P.left)
          (ParameterLaurentTrack.ambientTrack P.left) (specUnder.obj a) (-(i : ℤ))).hom ≫
        (stableHomotopyFunctor (-(i : ℤ))).map ((fineTelescopeComparison P).app a) =
      (negativeClassCorrection P i a).hom ≫
        (boundedFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom.app a := by
  have h := currentIteratedStableIso_inclusion (ParameterModels.ambient P.left)
    (ParameterLaurentTrack.ambientTrack P.left) i (specUnder.obj a) (-(i : ℤ))
  change (stableHomotopyFunctor (-(i : ℤ))).map
      ((currentStageInclusion P i).app (specUnder.obj a)) ≫ _ =
    (finiteStageStableIso (ParameterModels.ambient P.left) i (specUnder.obj a) (-(i : ℤ))).hom ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        ((iteratedStageInclusion P i).app (specUnder.obj a)) at h
  have hh := congrArg (fun z => (finiteNegativeKComparison P i).hom.app a ≫ z ≫
    (stableHomotopyFunctor (-(i : ℤ))).map ((fineTelescopeComparison P).app a)) h
  rw [← finiteNegativeKComparison_iterated_fine P i a]
  simpa only [currentNegativeKComparison_hom_app, negativeClassCorrection,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc,
    Iso.inv_hom_id_app_assoc] using hh

/-- Only the already established stages zero and one have trivial correction here. -/
theorem negativeClassCorrection_low_hom (i : ℕ) (hi : i ≤ 1)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (negativeClassCorrection P i a).hom = 𝟙 _ := by
  apply (cancel_mono ((boundedFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom.app a)).1
  simpa only [Category.id_comp] using
    (currentNegativeKComparison_fine_correction P i a).symm.trans
      (currentNegativeKComparison_low_fine P i hi a)

end GlobalParameterCoefficient

namespace GlobalSupportedParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The genuine finite-word correction, expressed on the unchanged original negative group. -/
def negativeClassCorrection (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (Bass.supportedNegativeKFunctor i).obj
      ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) ≅
      (Bass.supportedNegativeKFunctor i).obj
      ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) :=
  (finiteNegativeKComparison f i).app a ≪≫
    finiteStageStableIso (ParameterModels.supported f.left) i (specUnder.obj a) (-(i : ℤ)) ≪≫
      ((finiteNegativeKComparison f i).app a).symm

/-- The original current class retains its finite correction through the fine comparison. -/
@[reassoc]
theorem currentNegativeKComparison_fine_correction (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (currentNegativeKComparison f i).hom.app a ≫
        (currentIteratedStableIso (ParameterModels.supported f.left)
          (ParameterLaurentTrack.supportedTrack f.left) (specUnder.obj a) (-(i : ℤ))).hom ≫
        (stableHomotopyFunctor (-(i : ℤ))).map ((fineTelescopeComparison f).app a) =
      (negativeClassCorrection f i a).hom ≫
        (boundedFlatCoefficientSupportedNegativeKTelescopeComparison f i).hom.app a := by
  have h := currentIteratedStableIso_inclusion (ParameterModels.supported f.left)
    (ParameterLaurentTrack.supportedTrack f.left) i (specUnder.obj a) (-(i : ℤ))
  change (stableHomotopyFunctor (-(i : ℤ))).map
      ((currentStageInclusion f i).app (specUnder.obj a)) ≫ _ =
    (finiteStageStableIso (ParameterModels.supported f.left) i
      (specUnder.obj a) (-(i : ℤ))).hom ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        ((iteratedStageInclusion f i).app (specUnder.obj a)) at h
  have hh := congrArg (fun z => (finiteNegativeKComparison f i).hom.app a ≫ z ≫
    (stableHomotopyFunctor (-(i : ℤ))).map ((fineTelescopeComparison f).app a)) h
  rw [← finiteNegativeKComparison_iterated_fine f i a]
  simpa only [currentNegativeKComparison_hom_app, negativeClassCorrection,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc,
    Iso.inv_hom_id_app_assoc] using hh

/-- Only the already established stages zero and one have trivial correction here. -/
theorem negativeClassCorrection_low_hom (i : ℕ) (hi : i ≤ 1)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (negativeClassCorrection f i a).hom = 𝟙 _ := by
  apply (cancel_mono
    ((boundedFlatCoefficientSupportedNegativeKTelescopeComparison f i).hom.app a)).1
  simpa only [Category.id_comp] using
    (currentNegativeKComparison_fine_correction f i a).symm.trans
      (currentNegativeKComparison_low_fine f i hi a)

end GlobalSupportedParameterCoefficient

end Quillen.PerfectComplexes
