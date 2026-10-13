/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenWeak
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionForgetModel
public import Quillen.Waldhausen.SConstruction.Iterated.ZeroMap
public import Quillen.Topology.Prespectrum.MappingCone

/-!
# The original supported-section to relative-open null track

The actual section category with open-detected weak equivalences retains the original chosen
section zero. The literal support inclusion followed by the original change of weaknesses
has the whole nullhomotopy from the actual weak zero-to-section transformation. It descends
to a specified cone map with unchanged target face and cylinder values. Stability of this
section-level descent and comparison with the full open endpoint are separate obligations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open Waldhausen Waldhausen.Fibration Waldhausen.IteratedS
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original section category with its actual relative-open weak class and original zero. -/
def boundedFlatAffineSectionOpenModel : Model.{u + 1} :=
  ⟨Cat.of (BoundedFlatAffineSections R), boundedFlatAffineSectionOpenWaldhausen j⟩

/-- The identity section functor changes only the weak class, retaining the chosen zero. -/
def boundedFlatAffineSectionOpenModelMap :
    boundedFlatAffineSectionModel R ⟶ boundedFlatAffineSectionOpenModel j where
  functor := 𝟭 _
  exact := changeWeak_exact (boundedFlatAffineSectionOpenNested j)
  zero := rfl

/-- The original fine section prespectrum maps to the actual relative-open section prespectrum. -/
def boundedFlatAffineSectionOpenPrespectrumMap :
    boundedFlatAffineSectionPrespectrumFunctor.obj R ⟶
      prespectrum (boundedFlatAffineSectionOpenModel j) :=
  prespectrumMap (boundedFlatAffineSectionOpenModelMap j)

/-- The entire original weak transformation gives a coherent null track of support restriction. -/
def boundedFlatAffineSupportedSectionOpenNullHomotopy : LoopPrespectrum.Homotopy
    (boundedFlatAffineSupportedSectionForgetPrespectrumMap j ≫
      boundedFlatAffineSectionOpenPrespectrumMap j)
    (LoopPrespectrum.zeroHom (prespectrum (boundedFlatAffineSupportedSectionModel j))
      (prespectrum (boundedFlatAffineSectionOpenModel j))) := by
  have H := (prespectrumTransformationHomotopy
    (F := zeroHom (boundedFlatAffineSupportedSectionModel j) (boundedFlatAffineSectionOpenModel j))
    (G := boundedFlatAffineSupportedSectionForgetModelMap j ≫
      boundedFlatAffineSectionOpenModelMap j)
    (boundedFlatAffineSupportedSectionZeroToOpen j)
    (boundedFlatAffineSupportedSectionZeroToOpen_weak j)).symm
  have he : prespectrumMap (boundedFlatAffineSupportedSectionForgetModelMap j ≫
      boundedFlatAffineSectionOpenModelMap j) =
      boundedFlatAffineSupportedSectionForgetPrespectrumMap j ≫
        boundedFlatAffineSectionOpenPrespectrumMap j := prespectrumFunctor.map_comp _ _
  exact {
    level := H.level
    at_zero n x := (H.at_zero n x).trans (congrArg (fun f ↦ f.map n x) he)
    at_one n x := (H.at_one n x).trans (congrArg (fun f ↦ f.map n x)
      (prespectrumMap_zeroHom (boundedFlatAffineSupportedSectionModel j)
        (boundedFlatAffineSectionOpenModel j)))
    at_point := H.at_point
    comm := H.comm }

/-- The original support cone descends to the relative-open section model along this same track. -/
def boundedFlatAffineSupportedSectionOpenConeMap :
    LoopPrespectrum.mappingCone (boundedFlatAffineSupportedSectionForgetPrespectrumMap j) ⟶
      prespectrum (boundedFlatAffineSectionOpenModel j) :=
  LoopPrespectrum.mappingConeDesc (boundedFlatAffineSupportedSectionForgetPrespectrumMap j)
    (boundedFlatAffineSectionOpenPrespectrumMap j)
    (boundedFlatAffineSupportedSectionOpenNullHomotopy j)

/-- The original ambient section map is the unchanged target face of the actual cone descent. -/
theorem boundedFlatAffineSupportedSectionOpenConeMap_inclusion :
    LoopPrespectrum.mappingConeInclusion (boundedFlatAffineSupportedSectionForgetPrespectrumMap j) ≫
        boundedFlatAffineSupportedSectionOpenConeMap j =
      boundedFlatAffineSectionOpenPrespectrumMap j :=
  LoopPrespectrum.mappingConeInclusion_desc _ _ _

/-- Every original cone-cylinder value is the specified original section null track. -/
theorem boundedFlatAffineSupportedSectionOpenConeMap_cylinder
    (n : ℕ) (s : unitInterval)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSupportedSectionOpenConeMap j).map n
        (ReducedMappingCone.cylinder
          ((prespectrum (boundedFlatAffineSupportedSectionModel j)).point n)
          ((boundedFlatAffineSectionPrespectrumFunctor.obj R).point n)
          ((boundedFlatAffineSupportedSectionForgetPrespectrumMap j).map n) (s, x)) =
      (boundedFlatAffineSupportedSectionOpenNullHomotopy j).level n (s, x) := rfl

end Quillen.PerfectComplexes
