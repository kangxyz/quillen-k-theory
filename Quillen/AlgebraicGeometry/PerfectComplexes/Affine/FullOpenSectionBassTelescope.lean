/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassTower
public import Quillen.Topology.Prespectrum.TelescopeDiagram
public import Quillen.Topology.Prespectrum.TelescopeStableRepresentability

/-!
# The actual fine full-open Bass telescope

The original fine finite stages and their constructed seed transitions form the reduced
quotient telescope. All stage inclusions, level coordinates and cylinder heights remain literal.
Separation and finite stable representatives follow from the original Model-stage topology.
No stabilization or signed vanishing assertion for this fine telescope is used.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The reduced telescope of the original fine stages and original transitions. -/
def boundedFlatAffineFullOpenSectionBassTelescopeFunctor :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedFlatAffineFullOpenSectionBassDiagram j)
    (boundedFlatAffineFullOpenSectionBassTransition j)

/-- Every original fine stage enters at the zero face of its unchanged cylinder. -/
def boundedFlatAffineFullOpenSectionBassTelescopeInclusion (i : ℕ) :
    boundedFlatAffineFullOpenSectionBassDiagram j i ⟶
      boundedFlatAffineFullOpenSectionBassTelescopeFunctor j :=
  Telescope.diagramInclusion (boundedFlatAffineFullOpenSectionBassDiagram j)
    (boundedFlatAffineFullOpenSectionBassTransition j) i

/-- The original fine section diagram enters through its unchanged initial telescope face. -/
def boundedFlatAffineFullOpenSectionBassTelescopeInitial :
    boundedFlatAffineFullOpenSectionPrespectrumFunctor j ⟶
      boundedFlatAffineFullOpenSectionBassTelescopeFunctor j :=
  boundedFlatAffineFullOpenSectionBassTelescopeInclusion j 0

/-- Each actual level of the fine telescope carries its original reduced quotient topology. -/
instance boundedFlatAffineFullOpenSectionBassTelescope_spaceT1Space
    (a : Under R) (n : ℕ) :
    T1Space (((boundedFlatAffineFullOpenSectionBassTelescopeFunctor j).obj a).space n) :=
  Telescope.spaceT1Space
    (fun i ↦ (boundedFlatAffineFullOpenSectionBassDiagram j i).obj a)
    (fun i ↦ (boundedFlatAffineFullOpenSectionBassTransition j i).app a) n

/-- Actual coefficient maps retain both the finite stage map and the cylinder height. -/
theorem boundedFlatAffineFullOpenSectionBassTelescopeFunctor_map_cylinder
    {a b : Under R} (f : a ⟶ b) (n i : ℕ) (s : unitInterval)
    (x : ((boundedFlatAffineFullOpenSectionBassDiagram j i).obj a).space n) :
    ((boundedFlatAffineFullOpenSectionBassTelescopeFunctor j).map f).map n
        (Telescope.cylinder
          (fun k ↦ (boundedFlatAffineFullOpenSectionBassDiagram j k).obj a)
          (fun k ↦ (boundedFlatAffineFullOpenSectionBassTransition j k).app a) n i (s, x)) =
      Telescope.cylinder
        (fun k ↦ (boundedFlatAffineFullOpenSectionBassDiagram j k).obj b)
        (fun k ↦ (boundedFlatAffineFullOpenSectionBassTransition j k).app b) n i
        (s, ((boundedFlatAffineFullOpenSectionBassDiagram j i).map f).map n x) := rfl

/-- The stage inclusion is exactly the original cylinder's initial face at every level. -/
theorem boundedFlatAffineFullOpenSectionBassTelescopeInclusion_apply
    (i : ℕ) (a : Under R) (n : ℕ)
    (x : ((boundedFlatAffineFullOpenSectionBassDiagram j i).obj a).space n) :
    ((boundedFlatAffineFullOpenSectionBassTelescopeInclusion j i).app a).map n x =
      Telescope.cylinder
        (fun k ↦ (boundedFlatAffineFullOpenSectionBassDiagram j k).obj a)
        (fun k ↦ (boundedFlatAffineFullOpenSectionBassTransition j k).app a) n i (0, x) := rfl

/-- The unchanged original cylinder compares consecutive fine stage inclusions. -/
def boundedFlatAffineFullOpenSectionBassTelescopeInclusionHomotopy
    (a : Under R) (i : ℕ) :
    Homotopy ((boundedFlatAffineFullOpenSectionBassTelescopeInclusion j i).app a)
      ((boundedFlatAffineFullOpenSectionBassTransition j i).app a ≫
        (boundedFlatAffineFullOpenSectionBassTelescopeInclusion j (i + 1)).app a) :=
  Telescope.diagramInclusionHomotopy (boundedFlatAffineFullOpenSectionBassDiagram j)
    (boundedFlatAffineFullOpenSectionBassTransition j) a i

/-- The homotopy retains the whole original level, stage and height coordinate. -/
theorem boundedFlatAffineFullOpenSectionBassTelescopeInclusionHomotopy_apply
    (a : Under R) (i n : ℕ) (s : unitInterval)
    (x : ((boundedFlatAffineFullOpenSectionBassDiagram j i).obj a).space n) :
    (boundedFlatAffineFullOpenSectionBassTelescopeInclusionHomotopy j a i).level n (s, x) =
      Telescope.cylinder
        (fun k ↦ (boundedFlatAffineFullOpenSectionBassDiagram j k).obj a)
        (fun k ↦ (boundedFlatAffineFullOpenSectionBassTransition j k).app a) n i (s, x) := rfl

/-- Every signed stable class of the fine telescope has an actual finite-stage representative. -/
theorem boundedFlatAffineFullOpenSectionBassTelescope_exists_stable_representative
    (a : Under R) (d : ℤ)
    (x : stableHomotopyGroup
      ((boundedFlatAffineFullOpenSectionBassTelescopeFunctor j).obj a) d) :
    ∃ i : ℕ, ∃ y : stableHomotopyGroup
      ((boundedFlatAffineFullOpenSectionBassDiagram j i).obj a) d,
      (stableHomotopyFunctor d).map
        ((boundedFlatAffineFullOpenSectionBassTelescopeInclusion j i).app a) y = x :=
  Telescope.exists_stable_representative
    (fun i ↦ (boundedFlatAffineFullOpenSectionBassDiagram j i).obj a)
    (fun i ↦ (boundedFlatAffineFullOpenSectionBassTransition j i).app a) d x

end Quillen.PerfectComplexes
