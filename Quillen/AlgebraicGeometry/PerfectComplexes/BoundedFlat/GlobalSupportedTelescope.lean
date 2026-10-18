/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedAction
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedBassTelescope
public import Quillen.KTheory.Bass.ModelDiagramConnectivity
public import Quillen.Topology.Prespectrum.TelescopeStableEquivalence

/-!
# The actual supported global-section to coefficient-section Bass telescope comparison

The source iterates its original base seed. The target is the existing native supported
telescope. The unchanged restriction commutes strictly with those transitions and is stable
at every finite stage and on the actual quotient telescope.
-/
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
namespace SupportedTelescope

/-- The actual global row's original finite Bass iterates. -/
def globalDiagram (i : ℕ) : Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (supportedRow f ⋙ prespectrumFunctor)

/-- The original base scalar/null seed iterated at the same finite stage. -/
def globalTransition (i : ℕ) : globalDiagram f i ⟶ globalDiagram f (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R) (supportedLaurentAction f).track.seed i

/-- The original global-row telescope. -/
def globalTelescope : Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (globalDiagram f) (globalTransition f)

/-- The unchanged restriction at each finite stage. -/
def finiteRestriction (i : ℕ) :
    globalDiagram f i ⟶ boundedFlatCoefficientSupportedBassDiagram f i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor)

/-- Original seed compatibility gives the exact finite transition square. -/
theorem finiteRestriction_transition (i : ℕ) :
    finiteRestriction f i ≫ boundedFlatCoefficientSupportedBassTransition f i =
      globalTransition f i ≫ finiteRestriction f (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (supportedLaurentAction f).track.seed (boundedFlatCoefficientSupportedBassSeed f)
    (Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor)
    (supportedRowRestriction_seed f) i).symm

/-- Actual restriction into the existing native supported telescope. -/
def telescopeRestriction :
    globalTelescope f ⟶ boundedFlatCoefficientSupportedBassTelescopeFunctor f :=
  Telescope.diagramMap (globalDiagram f) (boundedFlatCoefficientSupportedBassDiagram f)
    (globalTransition f) (boundedFlatCoefficientSupportedBassTransition f)
    (finiteRestriction f) (finiteRestriction_transition f)

/-- Every original telescope cylinder retains its stage and full height. -/
theorem telescopeRestriction_cylinder (a : Under R) (n i : ℕ) (s : unitInterval)
    (x : ((globalDiagram f i).obj a).space n) :
    ((telescopeRestriction f).app a).map n
      (Telescope.cylinder (fun j => (globalDiagram f j).obj a)
        (fun j => (globalTransition f j).app a) n i (s, x)) =
    Telescope.cylinder (fun j => (boundedFlatCoefficientSupportedBassDiagram f j).obj a)
      (fun j => (boundedFlatCoefficientSupportedBassTransition f j).app a) n i
      (s, ((finiteRestriction f i).app a).map n x) :=
  Telescope.diagramMap_cylinder _ _ _ _ _ _ a n i s x

/-- Original stage inclusions commute with this same telescope map. -/
theorem telescopeRestriction_inclusion (i : ℕ) :
    Telescope.diagramInclusion (globalDiagram f) (globalTransition f) i ≫
      telescopeRestriction f =
    finiteRestriction f i ≫ boundedFlatCoefficientSupportedBassTelescopeInclusion f i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

end SupportedTelescope
end Quillen.PerfectComplexes.GlobalSectionChangeIndex
