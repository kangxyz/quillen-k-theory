/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassConeExcision
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescopeCone
public import Quillen.Topology.Prespectrum.TelescopeConeExcision

/-!
# Genuine signed cone exactness of the original section Bass telescope

Finite-stage growth and genuine excision, actual cone/telescope interchange, compact stable
representability and filtered exactness prove stable excision for the unchanged telescope
coefficient map. Its boundary is the existing original signed fiber boundary transported by
that same canonical comparison. Every finite-stage boundary is retained by its original cone
inclusion. No uniform telescope connectivity, replacement map or remaining excision premise
appears in these concrete conclusions.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The original coefficient-map cone-to-fiber comparison of the actual Bass telescope is stable.
-/
theorem boundedFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence :
    IsStableEquivalence (mappingConeFiberComparison (boundedFlatAffineSectionBassTelescopeMap f)) :=
  Telescope.coneFiberComparison_isStableEquivalence
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).naturality f)
    (fun i ↦ boundedFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence i f)

/-- The unchanged original signed cone boundary, now justified for the actual Bass telescope. -/
def boundedFlatAffineSectionBassTelescopeConeConnecting (d : ℤ) :
    stableHomotopyGroup (mappingCone (boundedFlatAffineSectionBassTelescopeMap f)) (d + 1) ⟶
      stableHomotopyGroup (boundedFlatAffineSectionBassTelescope R) d :=
  stableMappingConeConnecting (boundedFlatAffineSectionBassTelescopeMap f)
    (boundedFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence f) d

/-- Every original finite coefficient-cone stage retains exactly its existing signed boundary.
-/
@[reassoc] theorem boundedFlatAffineSectionBassTelescopeConeConnecting_stage (d : ℤ) (i : ℕ) :
    (stableHomotopyFunctor (d + 1)).map (boundedFlatAffineSectionBassConeStageMap f i) ≫
      boundedFlatAffineSectionBassTelescopeConeConnecting f d =
        stableMappingConeConnecting ((boundedFlatAffineSectionBassDiagram i).map f)
          (boundedFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence i f) d ≫
            (stableHomotopyFunctor d).map
              ((boundedFlatAffineSectionBassTelescopeInclusion i).app R) := by
  have he := Telescope.coneStableConnecting_eq_original
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).naturality f)
    (fun i ↦ boundedFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence i f) d
  refine (congrArg (fun δ ↦
    (stableHomotopyFunctor (d + 1)).map (boundedFlatAffineSectionBassConeStageMap f i) ≫ δ)
    he).symm.trans ?_
  exact Telescope.coneStableConnecting_stage
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).naturality f)
    (fun i ↦ boundedFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence i f) d i

/-- All recurring original cone-sequence positions are exact in every integer degree. -/
theorem boundedFlatAffineSectionBassTelescopeConeLongExactSequence (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor (d + 1)).map
      (mappingConeInclusion (boundedFlatAffineSectionBassTelescopeMap f)))
      (boundedFlatAffineSectionBassTelescopeConeConnecting f d) ∧
    Function.Exact (boundedFlatAffineSectionBassTelescopeConeConnecting f d)
      ((stableHomotopyFunctor d).map (boundedFlatAffineSectionBassTelescopeMap f)) ∧
    Function.Exact ((stableHomotopyFunctor d).map (boundedFlatAffineSectionBassTelescopeMap f))
      ((stableHomotopyFunctor d).map
        (mappingConeInclusion (boundedFlatAffineSectionBassTelescopeMap f))) :=
  stableMappingConeLongExactSequence (boundedFlatAffineSectionBassTelescopeMap f)
    (boundedFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence f) d

end Quillen.PerfectComplexes
