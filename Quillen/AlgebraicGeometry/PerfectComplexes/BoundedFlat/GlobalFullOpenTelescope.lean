/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalFullOpenSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalOpenTelescope
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionTelescope

/-! # Actual localization arrows on the original global Bass telescopes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex.FullOpenTelescope
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- Actual global open restriction at every original finite stage. -/
def finiteRestriction (i : ℕ) :
    OpenTelescope.globalDiagram f i ⟶ globalDiagram P i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (Functor.whiskerRight (globalOpenRestriction f) prespectrumFunctor)

/-- The unchanged original seed gives the finite transition square. -/
theorem finiteRestriction_transition (i : ℕ) :
    finiteRestriction f i ≫ globalTransition P i =
      OpenTelescope.globalTransition f i ≫ finiteRestriction f (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (openLaurentAction f).track.seed (globalLaurentAction P).track.seed
    (Functor.whiskerRight (globalOpenRestriction f) prespectrumFunctor)
    (globalOpenRestriction_seed f) i).symm

/-- Actual restriction from the coarse global telescope to the fine global open telescope. -/
def restriction : OpenTelescope.globalTelescope f ⟶ globalTelescope P :=
  Telescope.diagramMap (OpenTelescope.globalDiagram f) (globalDiagram P)
    (OpenTelescope.globalTransition f) (globalTransition P)
    (finiteRestriction f) (finiteRestriction_transition f)

/-- Actual restriction preserves every original stage and independent cylinder height. -/
theorem restriction_cylinder (a : Under R) (n i : ℕ) (t : unitInterval)
    (x : ((OpenTelescope.globalDiagram f i).obj a).space n) :
    ((restriction f).app a).map n
      (Telescope.cylinder (fun j => (OpenTelescope.globalDiagram f j).obj a)
        (fun j => (OpenTelescope.globalTransition f j).app a) n i (t, x)) =
    Telescope.cylinder (fun j => (globalDiagram P j).obj a)
      (fun j => (globalTransition P j).app a) n i
      (t, ((finiteRestriction f i).app a).map n x) :=
  Telescope.diagramMap_cylinder _ _ _ _ _ _ a n i t x

end Quillen.PerfectComplexes.GlobalSectionChangeIndex.FullOpenTelescope
