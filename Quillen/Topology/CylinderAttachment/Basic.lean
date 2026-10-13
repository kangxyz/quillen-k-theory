/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.DoubleMappingCylinder.Basic

/-!
# Attaching both ends of a cylinder to one space

For arbitrary maps `f₀ f₁ : A ⟶ B`, the ordinary pushout of their endpoint
map with `A × I` admits a symmetric height, zero on `B`. Its positive-height
subspace is the genuine open cylinder `A × (0,1)`. A small-height open collar
and this interior cover the entire attachment. The construction does not
require the two endpoint images in `B` to be disjoint or injective.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Topology
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.CylinderAttachment

/-- Distance in the interval to its pair of endpoints. -/
def endpointDistance (t : I) : ℝ := min (t : ℝ) (1 - t)

@[simp] theorem endpointDistance_zero : endpointDistance 0 = 0 := by
  norm_num [endpointDistance]

@[simp] theorem endpointDistance_one : endpointDistance 1 = 0 := by
  norm_num [endpointDistance]

theorem endpointDistance_nonneg (t : I) : 0 ≤ endpointDistance t :=
  le_min t.2.1 (sub_nonneg.mpr t.2.2)

theorem endpointDistance_pos_iff (t : I) :
    0 < endpointDistance t ↔ 0 < t ∧ t < 1 := by
  simp only [endpointDistance, lt_min_iff]
  change (0 < (t : ℝ) ∧ 0 < 1 - (t : ℝ)) ↔ (0 < (t : ℝ) ∧ (t : ℝ) < 1)
  constructor <;> rintro ⟨h₀, h₁⟩ <;> exact ⟨h₀, by linarith⟩

theorem continuous_endpointDistance : Continuous endpointDistance := by
  unfold endpointDistance
  fun_prop

variable {A B D : TopCat.{u}} (f₀ f₁ : A ⟶ B)

/-- The two endpoint maps into the same target space. -/
def endMap : TopCat.of (A ⊕ A) ⟶ B :=
  TopCat.ofHom ⟨Sum.elim f₀ f₁,
    continuous_sum_dom.mpr ⟨f₀.hom.continuous, f₁.hom.continuous⟩⟩

variable {l : A ⊗ TopCat.I ⟶ D} {e : B ⟶ D}
  (sq : IsPushout (Quillen.intervalEndpoints A) (endMap f₀ f₁) l e)

/-- Symmetric height on the unglued cylinder. -/
def heightCylinderMap : A ⊗ TopCat.I ⟶ TopCat.of (ULift.{u} ℝ) :=
  TopCat.ofHom ⟨fun z ↦ ULift.up (endpointDistance z.2.down),
    continuous_uliftUp.comp (continuous_endpointDistance.comp
      (continuous_uliftDown.comp continuous_snd))⟩

/-- Both endpoints have height zero, so height descends to a single target. -/
theorem height_square : Quillen.intervalEndpoints A ≫ heightCylinderMap =
    endMap f₀ f₁ ≫ TopCat.ofHom (ContinuousMap.const B (ULift.up (0 : ℝ))) := by
  apply ConcreteCategory.hom_ext
  rintro (a | a)
  · change ULift.up (endpointDistance 0) = ULift.up (0 : ℝ)
    rw [endpointDistance_zero]
  · change ULift.up (endpointDistance 1) = ULift.up (0 : ℝ)
    rw [endpointDistance_one]

/-- Symmetric height on the actual cylinder attachment. -/
def height : C(D, ℝ) :=
  ⟨fun d ↦ (sq.desc heightCylinderMap
    (TopCat.ofHom (ContinuousMap.const B (ULift.up (0 : ℝ)))) (height_square f₀ f₁) d).down,
    by fun_prop⟩

@[simp] theorem height_cylinder (a : A) (t : TopCat.I) :
    height f₀ f₁ sq (l (a, t)) = endpointDistance t.down :=
  congrArg (fun z : ULift.{u} ℝ ↦ z.down) (ConcreteCategory.congr_hom
    (sq.inl_desc heightCylinderMap _ (height_square f₀ f₁)) (a, t))

@[simp] theorem height_base (b : B) : height f₀ f₁ sq (e b) = 0 :=
  congrArg (fun z : ULift.{u} ℝ ↦ z.down) (ConcreteCategory.congr_hom
    (sq.inr_desc heightCylinderMap _ (height_square f₀ f₁)) b)

theorem height_nonneg (d : D) : 0 ≤ height f₀ f₁ sq d := by
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) d with ⟨⟨a, t⟩, ht⟩ | ⟨b, hb⟩
  · change l (a, t) = d at ht
    rw [← ht, height_cylinder]
    exact endpointDistance_nonneg t.down
  · change e b = d at hb
    rw [← hb, height_base]

/-- The open interior, separated from the attached base by positive height. -/
def interiorSet : Set D := {d | 0 < height f₀ f₁ sq d}

/-- The open neighborhood of the base cut out by a symmetric height bound. -/
def collarSet (cut : ℝ) : Set D := {d | height f₀ f₁ sq d < cut}

theorem interior_isOpen : IsOpen (interiorSet f₀ f₁ sq) :=
  isOpen_lt continuous_const (height f₀ f₁ sq).continuous

theorem collar_isOpen (cut : ℝ) : IsOpen (collarSet f₀ f₁ sq cut) :=
  isOpen_lt (height f₀ f₁ sq).continuous continuous_const

theorem collar_union_interior (cut : ℝ) (hcut : 0 < cut) :
    collarSet f₀ f₁ sq cut ∪ interiorSet f₀ f₁ sq = Set.univ := by
  ext d
  simp only [Set.mem_union, collarSet, interiorSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  by_cases h : height f₀ f₁ sq d < cut
  · exact Or.inl h
  · exact Or.inr (lt_of_lt_of_le hcut (le_of_not_gt h))

theorem collar_inter_interior (cut : ℝ) :
    collarSet f₀ f₁ sq cut ∩ interiorSet f₀ f₁ sq =
      {d | 0 < height f₀ f₁ sq d ∧ height f₀ f₁ sq d < cut} := by
  ext d
  exact and_comm

include sq in
/-- The open cylinder maps openly and injectively into the attachment. -/
theorem interior_isOpenEmbedding :
    IsOpenEmbedding (fun z : A × DoubleCylinder.OpenInterval ↦ l (z.1, ULift.up z.2.1)) :=
  (isOpenEmbedding_pushout_cell_compl sq (isClosedEmbedding_intervalEndpoints A)).comp
    (DoubleCylinder.cylinderInteriorHomeomorph A).isOpenEmbedding

/-- Every positive-height point has an interior cylinder coordinate. -/
theorem interior_surjective (d : D) (hd : d ∈ interiorSet f₀ f₁ sq) :
    ∃ z : A × DoubleCylinder.OpenInterval, l (z.1, ULift.up z.2.1) = d := by
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) d with ⟨⟨a, t⟩, ht⟩ | ⟨b, hb⟩
  · change l (a, t) = d at ht
    have hh : 0 < endpointDistance t.down := by
      change 0 < height f₀ f₁ sq d at hd
      rwa [← ht, height_cylinder] at hd
    refine ⟨(a, ⟨t.down, (endpointDistance_pos_iff _).mp hh⟩), ?_⟩
    cases t
    exact ht
  · change e b = d at hb
    change 0 < height f₀ f₁ sq d at hd
    rw [← hb, height_base] at hd
    exact False.elim (lt_irrefl _ hd)

/-- The interior chart with its exact open-subspace target. -/
def interiorMap : C(A × DoubleCylinder.OpenInterval, interiorSet f₀ f₁ sq) where
  toFun z := ⟨l (z.1, ULift.up z.2.1), by
    change 0 < height f₀ f₁ sq (l (z.1, ULift.up z.2.1))
    rw [height_cylinder]
    exact (endpointDistance_pos_iff _).mpr z.2.2⟩
  continuous_toFun := by fun_prop

/-- The actual interior of the attachment is the ordinary open cylinder. -/
def interiorHomeomorph : A × DoubleCylinder.OpenInterval ≃ₜ interiorSet f₀ f₁ sq := by
  have h : IsEmbedding (interiorMap f₀ f₁ sq) :=
    IsEmbedding.subtypeVal.of_comp_iff.mp (interior_isOpenEmbedding f₀ f₁ sq).isEmbedding
  apply h.toHomeomorphOfSurjective
  intro d
  obtain ⟨z, hz⟩ := interior_surjective f₀ f₁ sq d.1 d.2
  exact ⟨z, Subtype.ext hz⟩

@[simp] theorem interiorHomeomorph_apply (z : A × DoubleCylinder.OpenInterval) :
    (interiorHomeomorph f₀ f₁ sq z).1 = l (z.1, ULift.up z.2.1) := rfl

/-- In interior coordinates, the collar overlap is exactly two short open end bands. -/
theorem interior_preimage_collar (cut : ℝ) :
    (fun z : A × DoubleCylinder.OpenInterval ↦ l (z.1, ULift.up z.2.1)) ⁻¹'
      collarSet f₀ f₁ sq cut =
      {z | (z.2.1 : ℝ) < cut ∨ 1 - (z.2.1 : ℝ) < cut} := by
  ext z
  change height f₀ f₁ sq (l (z.1, ULift.up z.2.1)) < cut ↔ _
  rw [height_cylinder, endpointDistance, min_lt_iff]
  rfl

end Quillen.CylinderAttachment
