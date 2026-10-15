/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.Square
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassTelescopeOpenNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassOpenBoundary
public import Quillen.Topology.Prespectrum.TelescopeConeDescentStable

/-!
# The original support-to-relative-open Bass telescope cofiber comparison

The original supported telescope forget map and the matching original coarse relative-open
map carry the constructed whole telescope null family. Its actual cone descent is stable:
the original finite descents are stable, and the actual finite Model stages supply T1.
Finite original excision also supplies the original signed telescope boundary. No uniform
telescope connectivity, seed stabilization or replacement by the full-open endpoint is assumed.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Descend the unchanged support-forgetting telescope cone using the constructed whole null. -/
def boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap :
    mappingConeDiagram (boundedFlatAffineSupportedSectionBassTelescopeForget j) ⟶
      boundedFlatAffineSectionOpenBassTelescopeFunctor j :=
  mappingConeDescTransformation (boundedFlatAffineSupportedSectionBassTelescopeForget j)
    (boundedFlatAffineSectionBassTelescopeOpen j)
    (boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).homotopy
    (boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).naturality

/-- The actual target face is the original ambient-to-relative-open telescope map. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap_inclusion (a : Under R) :
    mappingConeInclusion ((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a) ≫
        (boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap j).app a =
      (boundedFlatAffineSectionBassTelescopeOpen j).app a := mappingConeInclusion_desc _ _ _

/-- The exact original supported telescope cone descent is stable in every signed degree. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap j).app a) := by
  let : ∀ i k, T1Space (((boundedFlatAffineSupportedSectionBassDiagram j i).obj a).space k) :=
    fun i k ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatAffineSupportedSectionModelFunctor j) a k
  let : ∀ i k, T1Space (((boundedFlatAffineSectionBassDiagram i).obj a.right).space k) :=
    fun i k ↦ modelDiagramIterateSpaceT1Space laurentSquareFunctor i
      boundedFlatAffineSectionModelFunctor a.right k
  let : ∀ i k, T1Space (((boundedFlatAffineSectionOpenBassDiagram j i).obj a).space k) :=
    fun i k ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatAffineSectionOpenModelFunctor j) a k
  change IsStableEquivalence (mappingConeDesc
    ((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a)
    ((boundedFlatAffineSectionBassTelescopeOpen j).app a)
    ((boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).homotopy a))
  rw [boundedFlatAffineSupportedSectionBassTelescopeOpenNull_homotopy]
  exact Telescope.coneDesc_isStableEquivalence
    (fun n ↦ (boundedFlatAffineSupportedSectionBassDiagram j n).obj a)
    (fun n ↦ (boundedFlatAffineSupportedSectionBassTransition j n).app a)
    (fun n ↦ (boundedFlatAffineSectionBassDiagram n).obj a.right)
    (fun n ↦ (boundedFlatAffineSectionBassTransition n).app a.right)
    (fun n ↦ (boundedFlatAffineSectionOpenBassDiagram j n).obj a)
    (fun n ↦ (boundedFlatAffineSectionOpenBassTransition j n).app a)
    (fun n ↦ (boundedFlatAffineSupportedSectionBassForget j n).app a)
    (fun n ↦ (boundedFlatAffineSectionBassOpen j n).app a)
    (fun n ↦ congrArg (fun f ↦ f.app a)
      (boundedFlatAffineSupportedSectionBassForget_transition j n))
    (fun n ↦ congrArg (fun f ↦ f.app a)
      (boundedFlatAffineSectionBassOpen_transition j n))
    (fun n ↦ (boundedFlatAffineSupportedSectionBassOpenNull j n).homotopy a)
    (fun n m r x ↦ boundedFlatAffineSupportedSectionBassOpenNull_transition j n a m r x)
    (fun n ↦ boundedFlatAffineSupportedSectionBassOpenConeMap_isStableEquivalence j n a)

/-- Actual finite supported excision supplies the original telescope cone-fiber comparison. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeForget_coneFiber_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence (mappingConeFiberComparison
      ((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a)) := by
  let : ∀ i k, T1Space (((boundedFlatAffineSupportedSectionBassDiagram j i).obj a).space k) :=
    fun i k ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatAffineSupportedSectionModelFunctor j) a k
  let : ∀ i k, T1Space (((boundedFlatAffineSectionBassDiagram i).obj a.right).space k) :=
    fun i k ↦ modelDiagramIterateSpaceT1Space laurentSquareFunctor i
      boundedFlatAffineSectionModelFunctor a.right k
  exact Telescope.coneFiberComparison_isStableEquivalence
    (fun n ↦ (boundedFlatAffineSupportedSectionBassDiagram j n).obj a)
    (fun n ↦ (boundedFlatAffineSupportedSectionBassTransition j n).app a)
    (fun n ↦ (boundedFlatAffineSectionBassDiagram n).obj a.right)
    (fun n ↦ (boundedFlatAffineSectionBassTransition n).app a.right)
    (fun n ↦ (boundedFlatAffineSupportedSectionBassForget j n).app a)
    (fun n ↦ congrArg (fun f ↦ f.app a)
      (boundedFlatAffineSupportedSectionBassForget_transition j n))
    (fun n ↦ boundedFlatAffineSupportedSectionBassForget_coneFiber_isStableEquivalence j n a)

/-- The original signed boundary retains the exact supported telescope map and whole null lift. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap_connecting
    (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        ((boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap j).app a) ≫
      stableFiberConnecting ((boundedFlatAffineSectionBassTelescopeOpen j).app a) d =
    stableMappingConeConnecting ((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a)
      (boundedFlatAffineSupportedSectionBassTelescopeForget_coneFiber_isStableEquivalence j a) d ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift
          ((boundedFlatAffineSectionBassTelescopeOpen j).app a)
          ((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a)
          ((boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).homotopy a)) :=
  mappingConeDesc_connecting _ _ _
    (boundedFlatAffineSupportedSectionBassTelescopeForget_coneFiber_isStableEquivalence j a) d

/-- The original cone time and supported telescope height survive without reparameterization. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap_cylinder
    (a : Under R) (m i : ℕ) (r t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassDiagram j i).obj a).space m) :
    ((boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap j).app a).map m
      (Quillen.ReducedMappingCone.cylinder
        (((boundedFlatAffineSupportedSectionBassTelescopeFunctor j).obj a).point m)
        ((boundedFlatAffineSectionBassTelescope a.right).point m)
        (((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a).map m)
        (r, Telescope.cylinder
          (fun n ↦ (boundedFlatAffineSupportedSectionBassDiagram j n).obj a)
          (fun n ↦ (boundedFlatAffineSupportedSectionBassTransition j n).app a) m i (t, x))) =
      Telescope.cylinder (fun n ↦ (boundedFlatAffineSectionOpenBassDiagram j n).obj a)
        (fun n ↦ (boundedFlatAffineSectionOpenBassTransition j n).app a) m i
          (t, ((boundedFlatAffineSupportedSectionBassOpenNull j i).homotopy a).level m (r, x)) :=
  rfl

end Quillen.PerfectComplexes
