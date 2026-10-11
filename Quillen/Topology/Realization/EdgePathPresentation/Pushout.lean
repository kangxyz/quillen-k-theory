/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Realization.EdgePathPresentation.Collar
public import Quillen.Topology.Realization.SimplexBoundaryHEP
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Open collar neighborhoods in actual simplex-attachment pushouts

Closed embeddings are preserved by topological pushout. For a simplex
attachment, the barycentric boundary defect extends across the old space by
the constant value one. Its upper half defines a genuine open neighborhood
of that old space in the actual pushout topology.
-/
@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Convexity Topology Set
open scoped Topology unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen

/-- Cobase change of a closed embedding in actual topological spaces is a
closed embedding. The underlying injectivity and intersection statement are
proved in the set-theoretic pushout; closedness uses the colimit topology. -/
theorem isClosedEmbedding_pushout_right
    {A B C D : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) (hi : IsClosedEmbedding i) : IsClosedEmbedding j := by
  let sqT := sq.map (forget TopCat)
  have hj : Function.Injective j :=
    Types.pushoutCocone_inr_injective_of_isColimit sqT.isColimit hi.injective
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap j.hom.continuous hj ?_
  intro W hW
  have hleft : g ⁻¹' (j '' W) = i '' (f ⁻¹' W) := by
    ext b
    constructor
    · rintro ⟨c, hc, hcb⟩
      obtain ⟨a, hab, hac⟩ :=
        (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit sqT.isColimit
          hi.injective b c).mp hcb.symm
      change f a = c at hac
      exact ⟨a, by change f a ∈ W; rwa [hac], hab⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨f a, ha, (ConcreteCategory.congr_hom sq.w a).symm⟩
  rw [TopCat.isClosed_iff_of_isColimit sq.cocone sq.isColimit]
  rintro (_ | _ | _)
  · change IsClosed ((i ≫ g) ⁻¹' (j '' W))
    change IsClosed (i ⁻¹' (g ⁻¹' (j '' W)))
    rw [hleft]
    exact (hi.isClosedMap _ (hW.preimage f.hom.continuous)).preimage i.hom.continuous
  · change IsClosed (g ⁻¹' (j '' W))
    rw [hleft]
    exact hi.isClosedMap _ (hW.preimage f.hom.continuous)
  · change IsClosed (j ⁻¹' (j '' W))
    rw [Set.preimage_image_eq _ hj]
    exact hW

/-- The actual inclusion of a parametrized geometric simplex boundary is
closed, without any separation or compactness assumption on the parameters. -/
theorem isClosedEmbedding_parameterizedSimplexBoundary
    (X : TopCat.{u}) (n : ℕ) :
    IsClosedEmbedding (Quillen.parameterizedSimplexBoundaryInclusion X n) := by
  exact (Homeomorph.refl X).isClosedEmbedding.prodMap
    (isClosed_simplexBoundary n).isClosedEmbedding_subtypeVal

section SimplexAttachment

variable (X : TopCat.{u}) (n : ℕ) {C D : TopCat.{u}}
    {f : TopCat.of (X × simplexBoundary n) ⟶ C}
    {g : TopCat.of (X × StdSimplex ℝ (Fin (n + 1))) ⟶ D}
    {j : C ⟶ D}
    (sq : IsPushout (Quillen.parameterizedSimplexBoundaryInclusion X n) f g j)

/-- Extend the simplex's radial boundary coordinate across the old space,
where it has the constant value one. -/
def simplexAttachmentDefect : C(D, ℝ) := by
  let b : TopCat.of (X × StdSimplex ℝ (Fin (n + 1))) ⟶ TopCat.of (ULift.{u} ℝ) :=
    TopCat.ofHom ⟨fun z ↦ ULift.up (simplexBoundaryDefect z.2), by fun_prop⟩
  let c : C ⟶ TopCat.of (ULift.{u} ℝ) := TopCat.const (ULift.up (1 : ℝ))
  have h : Quillen.parameterizedSimplexBoundaryInclusion X n ≫ b = f ≫ c := by
    apply ConcreteCategory.hom_ext
    intro z
    change ULift.up (simplexBoundaryDefect z.2.1) = ULift.up (1 : ℝ)
    rw [(simplexBoundaryDefect_eq_one_iff z.2.1).mpr z.2.2]
  exact (⟨ULift.down, continuous_uliftDown⟩ : C(ULift.{u} ℝ, ℝ)).comp (sq.desc b c h).hom

@[simp] theorem simplexAttachmentDefect_cell (z : X × StdSimplex ℝ (Fin (n + 1))) :
    simplexAttachmentDefect X n sq (g z) = simplexBoundaryDefect z.2 := by
  simp only [simplexAttachmentDefect, ContinuousMap.comp_apply]
  rw [← ConcreteCategory.comp_apply, sq.inl_desc]
  rfl

@[simp] theorem simplexAttachmentDefect_old (c : C) :
    simplexAttachmentDefect X n sq (j c) = 1 := by
  simp only [simplexAttachmentDefect, ContinuousMap.comp_apply]
  rw [← ConcreteCategory.comp_apply, sq.inr_desc]
  rfl

/-- The old space together with the outer half of every attached simplex. -/
def simplexAttachmentCollar : Set D :=
  {z | (1 : ℝ) / 2 < simplexAttachmentDefect X n sq z}

theorem isOpen_simplexAttachmentCollar : IsOpen (simplexAttachmentCollar X n sq) :=
  isOpen_lt continuous_const (simplexAttachmentDefect X n sq).continuous

@[simp] theorem simplexAttachmentCollar_cell_iff
    (z : X × StdSimplex ℝ (Fin (n + 1))) :
    g z ∈ simplexAttachmentCollar X n sq ↔ z.2 ∈ simplexBoundaryCollar n := by
  change (1 : ℝ) / 2 < simplexAttachmentDefect X n sq (g z) ↔ _
  rw [simplexAttachmentDefect_cell]
  rfl

theorem range_old_subset_simplexAttachmentCollar :
    Set.range j ⊆ simplexAttachmentCollar X n sq := by
  rintro _ ⟨c, rfl⟩
  change (1 : ℝ) / 2 < simplexAttachmentDefect X n sq (j c)
  rw [simplexAttachmentDefect_old]
  norm_num

include sq in
/-- The previous space is a closed embedded subspace of the actual attachment. -/
theorem simplexAttachment_old_isClosedEmbedding : IsClosedEmbedding j :=
  isClosedEmbedding_pushout_right sq (isClosedEmbedding_parameterizedSimplexBoundary X n)

end SimplexAttachment

end Quillen
