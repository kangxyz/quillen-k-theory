/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterFineConnectingComparison
public import Quillen.KTheory.Bass.SchemeStageZeroComparison

/-! # Independently defined basic stage-zero classes through the actual comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.LoopPrespectrum Quillen.KTheory.Bass Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass.SchemeNaturalSeed
universe u
namespace Quillen.PerfectComplexes.ParameterFullCurrentNull
open GlobalSectionChangeIndex ParameterLaurentTrack
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The actual fiber Spec-row map preserves the independent original stage-zero inclusion. -/
theorem iterated_fine_initial_fiber :
    Functor.whiskerLeft specUnder (iteratedInitial (supportedTrack f.left)) ≫
        GlobalSupportedParameterCoefficient.fineTelescopeComparison f =
      Functor.whiskerRight
          ((parameterSupportedRowIso f).hom ≫ supportedRowRestriction f) prespectrumFunctor ≫
        boundedFlatCoefficientSupportedBassTelescopeInclusion f 0 := by
  apply NatTrans.ext
  funext a
  change _ = prespectrumFunctor.map ((parameterSupportedRowIso f).hom.app a ≫
    (supportedRowRestriction f).app a) ≫
      (boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a
  rw [prespectrumFunctor.map_comp]
  apply Hom.ext
  funext n
  ext x
  rfl

omit [IsOpenImmersion f.left] in
/-- The actual open Spec-row map preserves the independent original stage-zero inclusion. -/
theorem iterated_fine_initial_open :
    Functor.whiskerLeft specUnder (iteratedInitial (ambientTrack P.left)) ≫
        GlobalParameterCoefficient.fineTelescopeComparison P =
      Functor.whiskerRight (parameterCoefficientRestriction P) prespectrumFunctor ≫
        boundedFlatCoefficientAmbientBassTelescopeInclusion P 0 := by
  apply NatTrans.ext
  funext a
  change _ = prespectrumFunctor.map ((parameterRowModelIso P).hom.app a ≫
    (rowRestriction P).app a) ≫
      (boundedFlatCoefficientAmbientBassTelescopeInclusion P 0).app a
  rw [prespectrumFunctor.map_comp]
  apply Hom.ext
  funext n
  ext x
  rfl


/-- The basic current initial class is sent to the original fine fiber class, in every degree. -/
theorem current_fine_initial_fiber (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    (stableHomotopyFunctor d).map ((currentInitial (supportedTrack f.left)).app
      (specUnder.obj a)) ≫ (currentFineSupportComparison f a d).hom =
      (stableHomotopyFunctor d).map
          (prespectrumMap (((parameterSupportedRowIso f).hom ≫ supportedRowRestriction f).app a)) ≫
        (stableHomotopyFunctor d).map
          ((boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a) := by
  have h := currentIteratedStableIso_initial (ParameterModels.supported f.left)
    (supportedTrack f.left) (specUnder.obj a) d
  have hv := congrArg (stableHomotopyFunctor d).map
    (congrArg (fun η => η.app a) (iterated_fine_initial_fiber f))
  simp only [NatTrans.comp_app, Functor.map_comp] at hv
  change _ ≫ ((currentIteratedStableIso _ _ _ _).hom ≫ _) = _
  rw [← Category.assoc, h]
  exact hv

omit [IsOpenImmersion f.left] in
/-- The basic current initial open class is sent to the original fine open class. -/
theorem current_fine_initial_open (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    (stableHomotopyFunctor d).map ((currentInitial (ambientTrack P.left)).app
      (specUnder.obj a)) ≫ (currentFineOpenComparison f a d).hom =
      (stableHomotopyFunctor d).map (prespectrumMap ((parameterCoefficientRestriction P).app a)) ≫
        (stableHomotopyFunctor d).map
          ((boundedFlatCoefficientAmbientBassTelescopeInclusion P 0).app a) := by
  have h := currentIteratedStableIso_initial (ParameterModels.ambient P.left)
    (ambientTrack P.left) (specUnder.obj a) d
  have hv := congrArg (stableHomotopyFunctor d).map
    (congrArg (fun η => η.app a) (iterated_fine_initial_open (P := P)))
  simp only [NatTrans.comp_app, Functor.map_comp] at hv
  change _ ≫ ((currentIteratedStableIso _ _ _ _).hom ≫ _) = _
  rw [← Category.assoc, h]
  exact hv

end Quillen.PerfectComplexes.ParameterFullCurrentNull
