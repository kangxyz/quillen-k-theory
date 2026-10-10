/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Realization.EdgePathPresentation.Pushout

/-!
# Open interiors in a topological attachment

Away from the attaching locus, the cell map into a topological pushout is an
open embedding. Together with the collar deformation, this supplies the two
kinds of genuine open charts needed for path subdivision in an attachment.
-/
@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Topology

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen

section Pushout

variable {A B C D : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j)

include sq

/-- A cell point outside the attaching locus cannot be identified with a
different cell point by the pushout. -/
theorem pushout_cell_eq_of_not_mem_range {b b' : B}
    (hb : b ∉ Set.range i) (h : g b = g b') : b = b' := by
  classical
  let sqT := sq.map (forget TopCat)
  let test : B → Option B := fun x ↦ if x ∈ Set.range i then none else some x
  let bmap : (forget TopCat).obj B ⟶ Option B := ↾test
  let cmap : (forget TopCat).obj C ⟶ Option B := ↾fun _ ↦ none
  have w : (forget TopCat).map i ≫ bmap = (forget TopCat).map f ≫ cmap := by
    apply ConcreteCategory.hom_ext
    intro a
    change test (i a) = none
    simp [test]
  let dmap := sqT.desc bmap cmap w
  have hbmap (x : B) : dmap (g x) = test x :=
    ConcreteCategory.congr_hom (sqT.inl_desc bmap cmap w) x
  have heq := congrArg (fun z ↦ dmap z) h
  rw [hbmap b, hbmap b'] at heq
  by_cases hb' : b' ∈ Set.range i
  · simp only [test, ite_eq_right hb, ite_eq_left hb', Option.some_ne_none] at heq
  · simpa only [test, ite_eq_right hb, ite_eq_right hb', Option.some.injEq] using heq

/-- An open subset of the cell space disjoint from the attaching locus has
open image in the actual pushout. -/
theorem isOpen_pushout_cell_image (hi : Function.Injective i)
    (W : Set B) (hW : IsOpen W) (hdisj : W ⊆ (Set.range i)ᶜ) :
    IsOpen (g '' W) := by
  let sqT := sq.map (forget TopCat)
  have hleft : g ⁻¹' (g '' W) = W := by
    ext b
    constructor
    · rintro ⟨b', hb', hbb'⟩
      exact (pushout_cell_eq_of_not_mem_range sq (hdisj hb') hbb') ▸ hb'
    · exact fun hb ↦ ⟨b, hb, rfl⟩
  have hright : j ⁻¹' (g '' W) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro c
    rintro ⟨b, hb, hbc⟩
    obtain ⟨a, hab, _⟩ :=
      (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit sqT.isColimit hi b c).mp hbc
    exact hdisj hb ⟨a, hab⟩
  have hzero : i ⁻¹' W = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact hdisj ha (Set.mem_range_self a)
  rw [TopCat.isOpen_iff_of_isColimit sq.cocone sq.isColimit]
  rintro (_ | _ | _)
  · change IsOpen (i ⁻¹' (g ⁻¹' (g '' W)))
    rw [hleft, hzero]
    exact isOpen_empty
  · change IsOpen (g ⁻¹' (g '' W))
    rw [hleft]
    exact hW
  · change IsOpen (j ⁻¹' (g '' W))
    rw [hright]
    exact isOpen_empty

/-- The cell complement of a closed attaching locus embeds openly into the
pushout, with precisely its existing subspace topology. -/
theorem isOpenEmbedding_pushout_cell_compl (hi : IsClosedEmbedding i) :
    IsOpenEmbedding (fun b : ↥((Set.range i)ᶜ) ↦ g b.1) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact g.hom.continuous.comp continuous_subtype_val
  · intro b b' h
    apply Subtype.ext
    exact pushout_cell_eq_of_not_mem_range sq b.2 h
  · intro W hW
    have hemb : IsOpenEmbedding ((↑) : ↥((Set.range i)ᶜ) → B) :=
      hi.isClosed_range.isOpen_compl.isOpenEmbedding_subtypeVal
    have hW' : IsOpen (((↑) : ↥((Set.range i)ᶜ) → B) '' W) := hemb.isOpenMap W hW
    have hsub : ((↑) : ↥((Set.range i)ᶜ) → B) '' W ⊆ (Set.range i)ᶜ := by
      rintro _ ⟨b, _, rfl⟩
      exact b.2
    simpa only [Set.image_image, Function.comp_def] using
      isOpen_pushout_cell_image sq hi.injective _ hW' hsub

/-- The open cell complement is exactly the complement of the previous space
inside the pushout. -/
theorem range_pushout_cell_compl (hi : Function.Injective i) :
    Set.range (fun b : ↥((Set.range i)ᶜ) ↦ g b.1) = (Set.range j)ᶜ := by
  let sqT := sq.map (forget TopCat)
  ext z
  constructor
  · rintro ⟨b, rfl⟩ ⟨c, hc⟩
    obtain ⟨a, hab, _⟩ :=
      (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit sqT.isColimit hi b.1 c).mp hc.symm
    exact b.2 ⟨a, hab⟩
  · intro hz
    rcases Types.eq_or_eq_of_isPushout sqT z with ⟨b, hb⟩ | ⟨c, hc⟩
    · change g b = z at hb
      have hbi : b ∉ Set.range i := by
        rintro ⟨a, rfl⟩
        apply hz
        exact ⟨f a, (ConcreteCategory.congr_hom sq.w a).symm.trans hb⟩
      exact ⟨⟨b, hbi⟩, hb⟩
    · exact False.elim (hz ⟨c, hc⟩)

/-- A topological pushout along a closed embedding preserves the T₁
separation property. No Hausdorff assumption on either attached space is needed. -/
theorem t1Space_pushout_of_closedEmbedding [T1Space B] [T1Space C]
    (hi : IsClosedEmbedding i) : T1Space D := by
  let sqT := sq.map (forget TopCat)
  have hj := isClosedEmbedding_pushout_right sq hi
  constructor
  intro z
  rcases Types.eq_or_eq_of_isPushout sqT z with ⟨b, hb⟩ | ⟨c, hc⟩
  · change g b = z at hb
    subst z
    by_cases hbi : b ∈ Set.range i
    · obtain ⟨a, rfl⟩ := hbi
      have heq : g (i a) = j (f a) := ConcreteCategory.congr_hom sq.w a
      rw [heq]
      simpa only [Set.image_singleton] using hj.isClosedMap {f a} (isClosed_singleton)
    · have hleft : g ⁻¹' {g b} = {b} := by
        ext b'
        constructor
        · intro h
          exact (pushout_cell_eq_of_not_mem_range sq hbi h.symm).symm
        · intro h
          change g b' = g b
          exact congrArg g h
      have hright : j ⁻¹' {g b} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro c hc
        obtain ⟨a, hab, _⟩ :=
          (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit sqT.isColimit
            hi.injective b c).mp hc.symm
        exact hbi ⟨a, hab⟩
      have hzero : i ⁻¹' {b} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro a ha
        exact hbi ⟨a, ha⟩
      rw [TopCat.isClosed_iff_of_isColimit sq.cocone sq.isColimit]
      rintro (_ | _ | _)
      · change IsClosed (i ⁻¹' (g ⁻¹' {g b}))
        rw [hleft, hzero]
        exact isClosed_empty
      · change IsClosed (g ⁻¹' {g b})
        rw [hleft]
        exact isClosed_singleton
      · change IsClosed (j ⁻¹' {g b})
        rw [hright]
        exact isClosed_empty
  · change j c = z at hc
    subst z
    simpa only [Set.image_singleton] using hj.isClosedMap {c} (isClosed_singleton)

end Pushout

end Quillen
