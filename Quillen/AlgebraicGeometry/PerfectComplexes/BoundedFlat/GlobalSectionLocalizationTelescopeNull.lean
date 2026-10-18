/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionLocalizationNullSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalLocalizationTelescopeMaps

/-! # The same actual global localization null on the original seed telescope -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex.LocalizationTelescope
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The same complete finite localization nulls define the original coefficient telescope null. -/
def null :
    DiagramNullHomotopy (forget f)
      (openMap f) where
  homotopy a := Telescope.mapNullHomotopy
    (fun i ↦ (SupportedTelescope.globalDiagram f i).obj a)
    (fun i ↦ (SupportedTelescope.globalTransition f i).app a)
    (fun i ↦ (globalDiagram Q i).obj a)
    (fun i ↦ (globalTransition Q i).app a)
    (fun i ↦ (OpenTelescope.globalDiagram f i).obj a)
    (fun i ↦ (OpenTelescope.globalTransition f i).app a)
    (fun i ↦ (finiteForget f i).app a)
    (fun i ↦ (finiteOpen f i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a) (finiteForget_transition f i))
    (fun i ↦ congrArg (fun η ↦ η.app a) (finiteOpen_transition f i))
    (fun i ↦ (globalSupportedOpenFiniteNull f i).homotopy a)
    (fun i m s x ↦ (globalSupportedOpenFiniteNull_transition f i a m s x).symm)
  naturality {a b} g m s x := by
    induction x using Quot.inductionOn with
    | h z =>
      change Telescope.cylinder
          (fun i ↦ (OpenTelescope.globalDiagram f i).obj b)
          (fun i ↦ (OpenTelescope.globalTransition f i).app b) m z.1
          (z.2.1, ((OpenTelescope.globalDiagram f z.1).map g).map m
            (((globalSupportedOpenFiniteNull f z.1).homotopy a).level m (s, z.2.2))) =
        Telescope.cylinder
          (fun i ↦ (OpenTelescope.globalDiagram f i).obj b)
          (fun i ↦ (OpenTelescope.globalTransition f i).app b) m z.1
          (z.2.1, ((globalSupportedOpenFiniteNull f z.1).homotopy b).level m
            (s, ((SupportedTelescope.globalDiagram f z.1).map g).map m z.2.2))
      exact congrArg (fun y ↦ Telescope.cylinder
        (fun i ↦ (OpenTelescope.globalDiagram f i).obj b)
        (fun i ↦ (OpenTelescope.globalTransition f i).app b) m z.1 (z.2.1, y))
        ((globalSupportedOpenFiniteNull f z.1).naturality g m s z.2.2)

/-- The canonical null time and original telescope height stay independent. -/
theorem null_cylinder
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((SupportedTelescope.globalDiagram f i).obj a).space m) :
    ((null f).homotopy a).level m
      (s, Telescope.cylinder (fun k ↦ (SupportedTelescope.globalDiagram f k).obj a)
        (fun k ↦ (SupportedTelescope.globalTransition f k).app a) m i (t, x)) =
    Telescope.cylinder (fun k ↦ (OpenTelescope.globalDiagram f k).obj a)
      (fun k ↦ (OpenTelescope.globalTransition f k).app a) m i
        (t, ((globalSupportedOpenFiniteNull f i).homotopy a).level m (s, x)) := rfl

/-- Actual restriction preserves the entire telescope null and the independent height. -/
theorem null_restriction (a : Under R) (n : ℕ) (s : unitInterval)
    (x : ((SupportedTelescope.globalTelescope f).obj a).space n) :
    ((OpenTelescope.telescopeRestriction f).app a).map n
      (((null f).homotopy a).level n (s, x)) =
    ((boundedFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a).level n
      (s, ((SupportedTelescope.telescopeRestriction f).app a).map n x) := by
  induction x using Quot.inductionOn with
  | h z =>
    exact congrArg (fun y => Telescope.cylinder
      (fun i => (boundedFlatCoefficientOpenBassDiagram f i).obj a)
      (fun i => (boundedFlatCoefficientOpenBassTransition f i).app a) n z.1 (z.2.1, y))
      (globalSupportedOpenFiniteNull_restriction f z.1 a n s z.2.2)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex.LocalizationTelescope
