/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionOpenBassDiagram
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionOpenBassSeed
public import Quillen.Topology.Prespectrum.TelescopeDiagram

/-!
# The original relative-open Bass tower

The genuine coarse Model diagram and its proved original Laurent seed give the actual finite
transitions and quotient telescope. Every coefficient arrow keeps the original cylinder height.
The endpoint remains the relative-open coarse section Model on the fixed original pullback.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Each original coarse transition is the same Bass iterate of the constructed Laurent seed. -/
def boundedFlatAffineSectionOpenBassTransition (n : ℕ) :
    boundedFlatAffineSectionOpenBassDiagram j n ⟶
      boundedFlatAffineSectionOpenBassDiagram j (n + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedFlatAffineSectionOpenBassSeed j) n

/-- The actual reduced quotient telescope of the original relative-open Bass tower. -/
def boundedFlatAffineSectionOpenBassTelescopeFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedFlatAffineSectionOpenBassDiagram j)
    (boundedFlatAffineSectionOpenBassTransition j)

/-- Each original coarse stage enters at the initial face of its actual cylinder. -/
def boundedFlatAffineSectionOpenBassTelescopeInclusion (n : ℕ) :
    boundedFlatAffineSectionOpenBassDiagram j n ⟶
      boundedFlatAffineSectionOpenBassTelescopeFunctor j :=
  Telescope.diagramInclusion (boundedFlatAffineSectionOpenBassDiagram j)
    (boundedFlatAffineSectionOpenBassTransition j) n

/-- The original coarse section prespectrum enters at the unchanged stage-zero face. -/
def boundedFlatAffineSectionOpenBassTelescopeInitial :
    boundedFlatAffineSectionOpenPrespectrumFunctor j ⟶
      boundedFlatAffineSectionOpenBassTelescopeFunctor j :=
  boundedFlatAffineSectionOpenBassTelescopeInclusion j 0

/-- Actual coefficient maps retain every cylinder height and original finite-stage map. -/
theorem boundedFlatAffineSectionOpenBassTelescopeFunctor_map_cylinder
    {a b : Under R} (f : a ⟶ b) (k i : ℕ) (s : unitInterval)
    (x : ((boundedFlatAffineSectionOpenBassDiagram j i).obj a).space k) :
    ((boundedFlatAffineSectionOpenBassTelescopeFunctor j).map f).map k
        (Telescope.cylinder (fun n ↦ (boundedFlatAffineSectionOpenBassDiagram j n).obj a)
          (fun n ↦ (boundedFlatAffineSectionOpenBassTransition j n).app a) k i (s, x)) =
      Telescope.cylinder (fun n ↦ (boundedFlatAffineSectionOpenBassDiagram j n).obj b)
        (fun n ↦ (boundedFlatAffineSectionOpenBassTransition j n).app b) k i
          (s, ((boundedFlatAffineSectionOpenBassDiagram j i).map f).map k x) := rfl

end Quillen.PerfectComplexes
