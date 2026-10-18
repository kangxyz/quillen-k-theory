/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalOpenAction
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenBassTelescope
public import Quillen.KTheory.Bass.ModelDiagramConnectivity
public import Quillen.Topology.Prespectrum.TelescopeStableEquivalence

/-!
# The actual open global-section to coarse-open coefficient Bass telescope comparison

The source iterates its original base seed. The target is the existing native coarse-open
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
namespace OpenTelescope

/-- The actual global row's original finite Bass iterates. -/
def globalDiagram (i : ℕ) : Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (openRow f ⋙ prespectrumFunctor)

/-- The original base scalar/null seed iterated at the same finite stage. -/
def globalTransition (i : ℕ) : globalDiagram f i ⟶ globalDiagram f (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R) (openLaurentAction f).track.seed i

/-- The original global-row telescope. -/
def globalTelescope : Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (globalDiagram f) (globalTransition f)

/-- The unchanged restriction at each finite stage. -/
def finiteRestriction (i : ℕ) :
    globalDiagram f i ⟶ boundedFlatCoefficientOpenBassDiagram f i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (Functor.whiskerRight (openRowRestriction f) prespectrumFunctor)

/-- Original seed compatibility gives the exact finite transition square. -/
theorem finiteRestriction_transition (i : ℕ) :
    finiteRestriction f i ≫ boundedFlatCoefficientOpenBassTransition f i =
      globalTransition f i ≫ finiteRestriction f (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (openLaurentAction f).track.seed (boundedFlatCoefficientOpenBassSeed f)
    (Functor.whiskerRight (openRowRestriction f) prespectrumFunctor)
    (openRowRestriction_seed f) i).symm

/-- Actual restriction into the existing native coarse-open telescope. -/
def telescopeRestriction :
    globalTelescope f ⟶ boundedFlatCoefficientOpenBassTelescopeFunctor f :=
  Telescope.diagramMap (globalDiagram f) (boundedFlatCoefficientOpenBassDiagram f)
    (globalTransition f) (boundedFlatCoefficientOpenBassTransition f)
    (finiteRestriction f) (finiteRestriction_transition f)

/-- Every original telescope cylinder retains its stage and full height. -/
theorem telescopeRestriction_cylinder (a : Under R) (n i : ℕ) (s : unitInterval)
    (x : ((globalDiagram f i).obj a).space n) :
    ((telescopeRestriction f).app a).map n
      (Telescope.cylinder (fun j => (globalDiagram f j).obj a)
        (fun j => (globalTransition f j).app a) n i (s, x)) =
    Telescope.cylinder (fun j => (boundedFlatCoefficientOpenBassDiagram f j).obj a)
      (fun j => (boundedFlatCoefficientOpenBassTransition f j).app a) n i
      (s, ((finiteRestriction f i).app a).map n x) :=
  Telescope.diagramMap_cylinder _ _ _ _ _ _ a n i s x

/-- Original stage inclusions commute with this same telescope map. -/
theorem telescopeRestriction_inclusion (i : ℕ) :
    Telescope.diagramInclusion (globalDiagram f) (globalTransition f) i ≫
      telescopeRestriction f =
    finiteRestriction f i ≫ boundedFlatCoefficientOpenBassTelescopeInclusion f i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

end OpenTelescope
end Quillen.PerfectComplexes.GlobalSectionChangeIndex
