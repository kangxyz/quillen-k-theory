/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionBassTransitionNull
public import Quillen.KTheory.Bass.ModelDiagramConnectivity
public import Quillen.Topology.Prespectrum.TelescopeDiagram
public import Quillen.Topology.Prespectrum.TelescopeStableRepresentability

/-!
# Signed vanishing of the actual quotient-graded Bass telescope

The original graded Model diagram and its forward Laurent seed determine the unchanged strict
Bass tower and its reduced quotient telescope. Every stage inclusion induces zero on every
signed stable group because its actual next transition does. Finite stable representatives
then prove vanishing of the telescope groups, with the required T1 topology supplied by the
original Model-stage theorem. No individual stage-vanishing premise is used. Transfer to the
original restriction deficit and the full localization conclusion remain separate.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The finite stage is the literal Bass iterate of the original graded section diagram. -/
def boundedFlatAffineFullOpenGradedSectionBassDiagram (i : ℕ) :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j)

/-- The tower retains the actual iterated image of the original forward Laurent seed. -/
def boundedFlatAffineFullOpenGradedSectionBassTransition (i : ℕ) :
    boundedFlatAffineFullOpenGradedSectionBassDiagram j i ⟶
      boundedFlatAffineFullOpenGradedSectionBassDiagram j (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedFlatAffineFullOpenGradedSectionBassSeed j) i

/-- The original seed itself is the unchanged first transition. -/
theorem boundedFlatAffineFullOpenGradedSectionBassTransition_zero :
    boundedFlatAffineFullOpenGradedSectionBassTransition j 0 =
      boundedFlatAffineFullOpenGradedSectionBassSeed j := rfl

/-- The actual reduced telescope of the same graded stage objects and original transitions. -/
def boundedFlatAffineFullOpenGradedSectionBassTelescopeFunctor :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedFlatAffineFullOpenGradedSectionBassDiagram j)
    (boundedFlatAffineFullOpenGradedSectionBassTransition j)

/-- Each original stage enters at its unchanged zero cylinder face. -/
def boundedFlatAffineFullOpenGradedSectionBassTelescopeInclusion (i : ℕ) :
    boundedFlatAffineFullOpenGradedSectionBassDiagram j i ⟶
      boundedFlatAffineFullOpenGradedSectionBassTelescopeFunctor j :=
  Telescope.diagramInclusion (boundedFlatAffineFullOpenGradedSectionBassDiagram j)
    (boundedFlatAffineFullOpenGradedSectionBassTransition j) i

/-- Actual coefficient maps keep both the original stage map and the cylinder coordinate. -/
theorem boundedFlatAffineFullOpenGradedSectionBassTelescopeFunctor_map_cylinder
    {a b : Under R} (f : a ⟶ b) (n i : ℕ) (s : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionBassDiagram j i).obj a).space n) :
    ((boundedFlatAffineFullOpenGradedSectionBassTelescopeFunctor j).map f).map n
        (Telescope.cylinder
          (fun k ↦ (boundedFlatAffineFullOpenGradedSectionBassDiagram j k).obj a)
          (fun k ↦ (boundedFlatAffineFullOpenGradedSectionBassTransition j k).app a) n i (s, x)) =
      Telescope.cylinder
        (fun k ↦ (boundedFlatAffineFullOpenGradedSectionBassDiagram j k).obj b)
        (fun k ↦ (boundedFlatAffineFullOpenGradedSectionBassTransition j k).app b) n i
        (s, ((boundedFlatAffineFullOpenGradedSectionBassDiagram j i).map f).map n x) := rfl

/-- Every original stage inclusion induces zero in each integer-graded stable degree. -/
theorem boundedFlatAffineFullOpenGradedSectionBassTelescopeInclusion_stableMap_eq_zero
    (i : ℕ) (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).map
      ((boundedFlatAffineFullOpenGradedSectionBassTelescopeInclusion j i).app a) = 0 := by
  let E := fun k ↦ (boundedFlatAffineFullOpenGradedSectionBassDiagram j k).obj a
  let τ := fun k ↦ (boundedFlatAffineFullOpenGradedSectionBassTransition j k).app a
  change (stableHomotopyFunctor d).map (Telescope.inclusion E τ i) = 0
  have hi := Telescope.inclusion_transition_stableMap E τ (Nat.le_succ i) d
  rw [Telescope.transition_succ] at hi
  have hz : (stableHomotopyFunctor d).map (τ i) = 0 :=
    boundedFlatAffineFullOpenGradedSectionBassTransition_stableMap_eq_zero j i a d
  exact hi.trans (by rw [hz, CategoryTheory.Limits.zero_comp])

/-- Every actual telescope stable class vanishes, including all negative degrees. -/
theorem boundedFlatAffineFullOpenGradedSectionBassTelescope_stableClass_eq_zero
    (a : Under R) (d : ℤ)
    (x : stableHomotopyGroup
      ((boundedFlatAffineFullOpenGradedSectionBassTelescopeFunctor j).obj a) d) : x = 0 := by
  let E := fun k ↦ (boundedFlatAffineFullOpenGradedSectionBassDiagram j k).obj a
  let τ := fun k ↦ (boundedFlatAffineFullOpenGradedSectionBassTransition j k).app a
  let : ∀ i n, T1Space ((E i).space n) :=
    fun i n ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatAffineFullOpenGradedSectionModelFunctor j) a n
  obtain ⟨i, y, hy⟩ := Telescope.exists_stable_representative E τ d x
  have hi := boundedFlatAffineFullOpenGradedSectionBassTelescopeInclusion_stableMap_eq_zero
    j i a d
  exact hy.symm.trans ((ConcreteCategory.congr_hom hi y).trans rfl)

/-- The genuine signed stable groups of the original graded telescope are subsingletons. -/
theorem boundedFlatAffineFullOpenGradedSectionBassTelescope_stableGroup_subsingleton
    (a : Under R) (d : ℤ) :
    Subsingleton (stableHomotopyGroup
      ((boundedFlatAffineFullOpenGradedSectionBassTelescopeFunctor j).obj a) d) :=
  ⟨fun x y ↦ (boundedFlatAffineFullOpenGradedSectionBassTelescope_stableClass_eq_zero j a d x).trans
    (boundedFlatAffineFullOpenGradedSectionBassTelescope_stableClass_eq_zero j a d y).symm⟩

end Quillen.PerfectComplexes
