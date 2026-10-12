/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.CylinderAttachment.Overlap

/-!
# Actual closed pairs and excisive charts for a cylinder attachment

The base image is a genuine embedded subspace, because the two cylinder endpoints
form a closed embedding. The attaching maps need not be embeddings and their
images may meet. The verified collar deformations therefore give homotopy
equivalences of the actual image subspaces with the open collars.
-/

@[expose] public section
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Topology
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.CylinderAttachment

/-- The actual endpoint-image subspace of the original cylinder. -/
def sourceBoundary (A : TopCat.{u}) : Set (A × ULift.{u} unitInterval) :=
  Set.range (Quillen.intervalEndpoints A)

/-- The actual two-piece open endpoint collar in the original cylinder. -/
def sourceCollar (A : TopCat.{u}) (cut : ℝ) : Set (A × ULift.{u} unitInterval) :=
  {z | endpointDistance z.2.down < cut}

/-- The actual positive-height interior of the original cylinder. -/
def sourceInterior (A : TopCat.{u}) : Set (A × ULift.{u} unitInterval) :=
  {z | 0 < endpointDistance z.2.down}

/-- The two actual endpoint copies identify with their original image subspace. -/
def sourceBoundaryHomeomorph (A : TopCat.{u}) : (A ⊕ A) ≃ₜ sourceBoundary A :=
  (isClosedEmbedding_intervalEndpoints A).isEmbedding.toHomeomorph

theorem sourceBoundary_subset_collar (A : TopCat.{u}) (cut : ℝ) (hcut : 0 < cut) :
    sourceBoundary A ⊆ sourceCollar A cut := by
  rintro _ ⟨a | a, rfl⟩
  · change endpointDistance 0 < cut
    simpa using hcut
  · change endpointDistance 1 < cut
    simpa using hcut

theorem sourceCollar_isOpen (A : TopCat.{u}) (cut : ℝ) : IsOpen (sourceCollar A cut) :=
  isOpen_lt (continuous_endpointDistance.comp
    (continuous_uliftDown.comp continuous_snd)) continuous_const

theorem sourceInterior_isOpen (A : TopCat.{u}) : IsOpen (sourceInterior A) :=
  isOpen_lt continuous_const (continuous_endpointDistance.comp
    (continuous_uliftDown.comp continuous_snd))

theorem sourceInterior_union_collar (A : TopCat.{u}) (cut : ℝ) (hcut : 0 < cut) :
    sourceInterior A ∪ sourceCollar A cut = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro z
  by_cases h : endpointDistance z.2.down < cut
  · exact Or.inr h
  · exact Or.inl (lt_of_lt_of_le hcut (le_of_not_gt h))

/-- The original boundary-image inclusion into its open collar. -/
def sourceBoundaryToCollar (A : TopCat.{u}) (cut : ℝ) (hcut : 0 < cut) :
    C(sourceBoundary A, sourceCollar A cut) :=
  ⟨fun z ↦ ⟨z.val, sourceBoundary_subset_collar A cut hcut z.property⟩, by fun_prop⟩

/-- The original included boundary image is homotopy equivalent to its open collar. -/
def sourceBoundaryCollarEquiv (A : TopCat.{u}) (cut : ℝ)
    (hpos : 0 < cut) (hcut : cut ≤ 1 / 2) :
    ContinuousMap.HomotopyEquiv (sourceBoundary A) (sourceCollar A cut) :=
  (sourceBoundaryHomeomorph A).symm.toHomotopyEquiv.trans
    (collarCylinderStrongDeformationRetract A cut hpos hcut).toHomotopyEquiv

theorem sourceBoundaryCollarEquiv_toFun (A : TopCat.{u}) (cut : ℝ)
    (hpos : 0 < cut) (hcut : cut ≤ 1 / 2) :
    (sourceBoundaryCollarEquiv A cut hpos hcut).toFun =
      sourceBoundaryToCollar A cut hpos := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact congrArg (fun y : sourceBoundary A ↦ y.val)
    ((sourceBoundaryHomeomorph A).apply_symm_apply z)

/-- The interior of the original cylinder has its exact open product coordinates. -/
def sourceInteriorHomeomorph (A : TopCat.{u}) :
    A × DoubleCylinder.OpenInterval ≃ₜ sourceInterior A where
  toFun z := ⟨(z.1, ULift.up z.2.val), (endpointDistance_pos_iff _).mpr z.2.property⟩
  invFun z := (z.val.1, ⟨z.val.2.down, (endpointDistance_pos_iff _).mp z.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

variable {A B D : TopCat.{u}} (f₀ f₁ : A ⟶ B)
  {l : A ⊗ TopCat.I ⟶ D} {e : B ⟶ D}
  (sq : IsPushout (Quillen.intervalEndpoints A) (endMap f₀ f₁) l e)

/-- The original attached base, with its actual image-subspace topology. -/
def baseImage : Set D := Set.range e

/-- Closed endpoint attachment makes the original base homeomorphic to its image. -/
def baseImageHomeomorph : B ≃ₜ baseImage (e := e) :=
  (isClosedEmbedding_pushout_right sq
    (isClosedEmbedding_intervalEndpoints A)).isEmbedding.toHomeomorph

theorem baseImage_subset_collar (cut : ℝ) (hcut : 0 < cut) :
    baseImage (e := e) ⊆ collarSet f₀ f₁ sq cut := by
  rintro _ ⟨b, rfl⟩
  change height f₀ f₁ sq (e b) < cut
  simpa using hcut

/-- The original included base image, regarded as a map into the open collar. -/
def baseImageToCollar (cut : ℝ) (hcut : 0 < cut) :
    C(baseImage (e := e), collarSet f₀ f₁ sq cut) :=
  ⟨fun z ↦ ⟨z.val, baseImage_subset_collar f₀ f₁ sq cut hcut z.property⟩, by fun_prop⟩

/-- The verified collar deformation gives the actual image-subspace inclusion as an equivalence. -/
def baseImageCollarEquiv (cut : ℝ) (hpos : 0 < cut) (hcut : cut ≤ 1 / 2) :
    ContinuousMap.HomotopyEquiv (baseImage (e := e)) (collarSet f₀ f₁ sq cut) :=
  (baseImageHomeomorph f₀ f₁ sq).symm.toHomotopyEquiv.trans
    (collarStrongDeformationRetract cut f₀ f₁ sq hpos hcut).toHomotopyEquiv

theorem baseImageCollarEquiv_toFun (cut : ℝ) (hpos : 0 < cut) (hcut : cut ≤ 1 / 2) :
    (baseImageCollarEquiv f₀ f₁ sq cut hpos hcut).toFun =
      baseImageToCollar f₀ f₁ sq cut hpos := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact congrArg (fun y : baseImage (e := e) ↦ y.val)
    ((baseImageHomeomorph f₀ f₁ sq).apply_symm_apply z)

include sq in
/-- The original characteristic map sends the actual boundary into the actual base image. -/
theorem cell_mapsTo_boundary : Set.MapsTo l (sourceBoundary A) (baseImage (e := e)) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨endMap f₀ f₁ a, (ConcreteCategory.congr_hom sq.w a).symm⟩

theorem cell_mapsTo_collar (cut : ℝ) :
    Set.MapsTo l (sourceCollar A cut) (collarSet f₀ f₁ sq cut) := by
  rintro ⟨a, t⟩ hz
  change height f₀ f₁ sq (l (a, t)) < cut
  rwa [height_cylinder]

theorem cell_mapsTo_interior :
    Set.MapsTo l (sourceInterior A) (interiorSet f₀ f₁ sq) := by
  rintro ⟨a, t⟩ hz
  change 0 < height f₀ f₁ sq (l (a, t))
  rwa [height_cylinder]

/-- The original cell map is a genuine homeomorphism on the excisive interiors. -/
def cellInteriorHomeomorph : sourceInterior A ≃ₜ interiorSet f₀ f₁ sq :=
  (sourceInteriorHomeomorph A).symm.trans (interiorHomeomorph f₀ f₁ sq)

@[simp]
theorem cellInteriorHomeomorph_apply (z : sourceInterior A) :
    (cellInteriorHomeomorph f₀ f₁ sq z).val = l z.val := rfl

/-- The actual interior chart identifies the original collar intersections. -/
theorem cellInteriorHomeomorph_mem_collar (cut : ℝ) (z : sourceInterior A) :
    z.val ∈ sourceCollar A cut ↔
      (cellInteriorHomeomorph f₀ f₁ sq z).val ∈ collarSet f₀ f₁ sq cut := by
  rcases z with ⟨⟨a, t⟩, hz⟩
  change endpointDistance t.down < cut ↔ height f₀ f₁ sq (l (a, t)) < cut
  rw [height_cylinder]

/-- The actual restricted cell map is a homeomorphism of the two nested collar intersections. -/
def cellInteriorCollarHomeomorph (cut : ℝ) :
    {z : sourceInterior A // z.val ∈ sourceCollar A cut} ≃ₜ
      {z : interiorSet f₀ f₁ sq // z.val ∈ collarSet f₀ f₁ sq cut} :=
  (cellInteriorHomeomorph f₀ f₁ sq).subtype
    (cellInteriorHomeomorph_mem_collar f₀ f₁ sq cut)

end Quillen.CylinderAttachment
