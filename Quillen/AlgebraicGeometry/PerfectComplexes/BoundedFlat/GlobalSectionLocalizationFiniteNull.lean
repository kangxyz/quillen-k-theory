/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionLocalizationNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedBassTower

/-! # Actual finite Bass iterates preserve the complete original restriction null -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- An actual time slice of the unchanged global null. -/
def globalSupportedOpenNullTimeSlice (s : unitInterval) :
    supportedRow f ⋙ prespectrumFunctor ⟶ openRow f ⋙ prespectrumFunctor :=
  diagramHomotopyAt
    (η := Functor.whiskerRight (supportedRowForget f) prespectrumFunctor ≫
      Functor.whiskerRight (openRowChangeWeak f) prespectrumFunctor)
    (θ := diagramZeroMap (supportedRow f ⋙ prespectrumFunctor)
      (openRow f ⋙ prespectrumFunctor))
    (globalSupportedOpenNull f).homotopy (globalSupportedOpenNull f).naturality s

/-- The entire original null time slice commutes with the actual restriction maps. -/
theorem globalSupportedOpenNull_timeSlice (s : unitInterval) :
    globalSupportedOpenNullTimeSlice f s ≫
      Functor.whiskerRight (openRowRestriction f) prespectrumFunctor =
    Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor ≫
      boundedFlatCoefficientSupportedOpenNullTimeSlice f s := by
  apply NatTrans.ext
  funext a
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact globalSupportedOpenNull_restriction f a n s x

/-- Iterate the original global null without selecting a new track. -/
def globalSupportedOpenFiniteNull (i : ℕ) :=
  strictDiagramIterateNull (laurentUnderSquareFunctor R) (globalSupportedOpenNull f) i

/-- Every finite-stage restriction retains all original null times and level values. -/
theorem globalSupportedOpenFiniteNull_restriction (i : ℕ) (a : Under R) (n : ℕ)
    (s : unitInterval)
    (x : (((strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
      (supportedRow f ⋙ prespectrumFunctor)).obj a).space n) :
    (((strictDiagramIterate (laurentUnderSquareFunctor R) i).map
        (Functor.whiskerRight (openRowRestriction f) prespectrumFunctor)).app a).map n
      (((globalSupportedOpenFiniteNull f i).homotopy a).level n (s, x)) =
    ((boundedFlatCoefficientSupportedBassOpenNull f i).homotopy a).level n
      (s, (((strictDiagramIterate (laurentUnderSquareFunctor R) i).map
        (Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor)).app a).map n x) := by
  have hG := strictDiagramIterateNull_level (laurentUnderSquareFunctor R)
    (globalSupportedOpenNull f) i a n s x
  have hF := strictDiagramIterateNull_level (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedOpenDiagramNull f) i a n s
    ((((strictDiagramIterate (laurentUnderSquareFunctor R) i).map
      (Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor)).app a).map n x)
  have h := congrArg (fun η =>
    (((strictDiagramIterate (laurentUnderSquareFunctor R) i).map η).app a).map n x)
      (globalSupportedOpenNull_timeSlice f s)
  simp only [Functor.map_comp, NatTrans.comp_app] at h
  exact (congrArg (fun y =>
    (((strictDiagramIterate (laurentUnderSquareFunctor R) i).map
      (Functor.whiskerRight (openRowRestriction f) prespectrumFunctor)).app a).map n y) hG).trans
        (h.trans hF.symm)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
