/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedParameterCoefficientTelescope
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedFineTelescopeComparison
public import Quillen.KTheory.Bass.SchemeStageInclusionComparison

/-!
# Original supported finite stages in the current parameter telescope

The actual supported integral Spec-row isomorphism and original section restriction
transport the proved fine inclusion range to the original iterated parameter
tower. The genuine finite-stage and telescope comparisons then give the same
range for the independent current-stage inclusion. No conjugating word is
identified with an identity, and no class map is defined by a telescope inverse.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalSupportedParameterCoefficient
open GlobalSectionChangeIndex GlobalSectionChangeIndex.SupportedTelescope SchemeNaturalSeed
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The literal inclusion into the original iterated-seed parameter telescope. -/
def iteratedStageInclusion (i : ℕ) :
    (strictDiagramIterate squareFunctor i).obj (parameterDiagram f) ⟶ parameterTelescope f.left :=
  Telescope.diagramInclusion (fun j => (strictDiagramIterate squareFunctor j).obj
    (parameterDiagram f))
    (strictDiagramTransition squareFunctor (seed (ParameterLaurentTrack.supportedTrack f.left))) i

/-- The literal inclusion into the independently defined current-stage parameter telescope. -/
def currentStageInclusion (i : ℕ) :
    (strictDiagramIterate squareFunctor i).obj (parameterDiagram f) ⟶
      currentTelescope (ParameterLaurentTrack.supportedTrack f.left) :=
  Telescope.diagramInclusion (fun j => (strictDiagramIterate squareFunctor j).obj
    (parameterDiagram f)) (currentTransition (ParameterLaurentTrack.supportedTrack f.left)) i

/-- The actual Spec comparison keeps the original stage inclusion at its original height zero. -/
theorem iteratedStageInclusion_telescopeIso (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (iteratedStageInclusion f i).app (specUnder.obj a) ≫ (telescopeIso f).hom.app a =
      (finiteIso f i).hom.app a ≫
        (Telescope.diagramInclusion (globalDiagram f) (globalTransition f) i).app a := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  rfl

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- Original global stage inclusions have the exact fine stable range. -/
theorem globalStageInclusion_isIso_of_le (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) (hd : -(i : ℤ) ≤ d) :
    IsIso ((stableHomotopyFunctor d).map
      ((Telescope.diagramInclusion (globalDiagram f) (globalTransition f) i).app a)) := by
  let H := stableHomotopyFunctor d
  let : IsIso (H.map ((telescopeRestriction f).app a)) :=
    telescopeRestriction_isStableEquivalence f a d
  let : IsIso (H.map ((finiteRestriction f i).app a)) :=
    finiteRestriction_isStableEquivalence f i a d
  let : IsIso (H.map ((boundedFlatCoefficientSupportedBassTelescopeInclusion f i).app a)) :=
    boundedFlatCoefficientSupportedBassTelescopeInclusion_isIso_of_le f i a d hd
  have h := congrArg H.map (congrArg (fun η => η.app a)
    (telescopeRestriction_inclusion f i))
  simp only [NatTrans.comp_app, Functor.map_comp] at h
  rw [← isIso_comp_right_iff _ (H.map ((telescopeRestriction f).app a)), h]
  infer_instance

/-- The actual iterated parameter inclusion is invertible in every original finite-stage range. -/
theorem iteratedStageInclusion_isIso_of_le (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) (hd : -(i : ℤ) ≤ d) :
    IsIso ((stableHomotopyFunctor d).map
      ((iteratedStageInclusion f i).app (specUnder.obj a))) := by
  let H := stableHomotopyFunctor d
  let : IsIso (H.map
      ((Telescope.diagramInclusion (globalDiagram f) (globalTransition f) i).app a)) :=
    globalStageInclusion_isIso_of_le f i a d hd
  have h := congrArg H.map (iteratedStageInclusion_telescopeIso f i a)
  simp only [Functor.map_comp] at h
  rw [← isIso_comp_right_iff _ (H.map ((telescopeIso f).hom.app a)), h]
  infer_instance

/-- The independent current inclusion is invertible in the same range without erasing its word. -/
theorem currentStageInclusion_isIso_of_le (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) (hd : -(i : ℤ) ≤ d) :
    IsIso ((stableHomotopyFunctor d).map
      ((currentStageInclusion f i).app (specUnder.obj a))) :=
  (model_currentInclusion_isIso_iff_iteratedInclusion (ParameterModels.supported f.left)
    (ParameterLaurentTrack.supportedTrack f.left) i (specUnder.obj a) d).mpr
      (iteratedStageInclusion_isIso_of_le f i a d hd)

end Quillen.PerfectComplexes.GlobalSupportedParameterCoefficient
