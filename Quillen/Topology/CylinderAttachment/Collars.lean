/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.CylinderAttachment.Basic
public import Quillen.Topology.DeformationRetract.FiberwisePushout
public import Mathlib.Topology.Piecewise

/-!
# A strong deformation collar of a cylinder attachment

For any positive cutoff at most one half, the symmetric-height collar of an
attachment of both cylinder ends to one space strongly deformation retracts
onto that space. The two disjoint half-open cylinder pieces contract to their
respective endpoints. Their joint deformation descends through the actual
open restriction of the original pushout.
-/
@[expose] public section

open Topology

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.CylinderAttachment

/-- The two half-open cylinder pieces forming a collar before attachment. -/
abbrev CollarCylinder (A : TopCat.{u}) (cut : ℝ) : TopCat.{u} :=
  TopCat.of {z : A × ULift.{u} I // endpointDistance z.2.down < cut}

variable (A : TopCat.{u}) (cut : ℝ)

/-- The endpoint pair included into the two-piece collar cylinder. -/
def collarEndpoints (hcut : 0 < cut) : TopCat.of (A ⊕ A) ⟶ CollarCylinder A cut :=
  TopCat.ofHom ⟨fun a ↦ ⟨Quillen.intervalEndpoints A a, by
    rcases a with a | a
    · change endpointDistance 0 < cut
      simpa using hcut
    · change endpointDistance 1 < cut
      simpa using hcut⟩, by fun_prop⟩

/-- The two ends of a short collar are separated by a clopen partition. -/
theorem collarCylinder_left_isClopen (hcut : cut ≤ 1 / 2) :
    IsClopen {z : CollarCylinder A cut | (z.1.2.down : ℝ) < cut} := by
  have hc : {z : CollarCylinder A cut | ¬ (z.1.2.down : ℝ) < cut} =
      {z : CollarCylinder A cut | 1 - (z.1.2.down : ℝ) < cut} := by
    ext z
    change (¬ (z.1.2.down : ℝ) < cut) ↔ 1 - (z.1.2.down : ℝ) < cut
    have hz := z.2
    change min (z.1.2.down : ℝ) (1 - (z.1.2.down : ℝ)) < cut at hz
    rw [min_lt_iff] at hz
    constructor
    · intro hn
      exact hz.resolve_left hn
    · intro hr hl
      linarith
  refine ⟨?_, isOpen_lt (by fun_prop) continuous_const⟩
  apply isOpen_compl_iff.mp
  change IsOpen {z : CollarCylinder A cut | ¬ (z.1.2.down : ℝ) < cut}
  rw [hc]
  exact isOpen_lt (by fun_prop) continuous_const

/-- Continuous choice of the endpoint component in the two-piece collar. -/
def collarCylinderRetraction (hcut : cut ≤ 1 / 2) :
    CollarCylinder A cut ⟶ TopCat.of (A ⊕ A) := by
  classical
  exact TopCat.ofHom ⟨fun z ↦ if (z.1.2.down : ℝ) < cut then Sum.inl z.1.1 else Sum.inr z.1.1,
    Continuous.if (by
      intro z hz
      rw [(collarCylinder_left_isClopen A cut hcut).frontier_eq] at hz
      exact False.elim hz) (by fun_prop) (by fun_prop)⟩

/-- The simultaneous contraction of the left and right interval pieces. -/
def collarCylinderDeformation (hcut : cut ≤ 1 / 2) :
    CollarCylinder A cut ⊗ TopCat.I ⟶ CollarCylinder A cut := by
  classical
  refine TopCat.ofHom ⟨fun p ↦ ⟨(p.1.1.1, ULift.up
    (if (p.1.1.2.down : ℝ) < cut then p.2.down * p.1.1.2.down
      else σ (p.2.down * σ p.1.1.2.down))), ?_⟩, ?_⟩
  · split_ifs with hl
    · apply lt_of_le_of_lt (min_le_left _ _)
      exact lt_of_le_of_lt (show ((p.2.down * p.1.1.2.down : I) : ℝ) ≤
        (p.1.1.2.down : ℝ) from unitInterval.mul_le_right) hl
    · have hr : 1 - (p.1.1.2.down : ℝ) < cut :=
        (min_lt_iff.mp p.1.2).resolve_left hl
      apply lt_of_le_of_lt (min_le_right _ _)
      have hm := (unitInterval.mul_le_right : p.2.down * σ p.1.1.2.down ≤ σ p.1.1.2.down)
      change (p.2.down : ℝ) * (1 - (p.1.1.2.down : ℝ)) ≤
        1 - (p.1.1.2.down : ℝ) at hm
      change 1 - (1 - (p.2.down : ℝ) * (1 - (p.1.1.2.down : ℝ))) < cut
      linarith
  · apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply continuous_uliftUp.comp
      apply Continuous.if
      · intro p hp
        have hc := (collarCylinder_left_isClopen A cut hcut).preimage
          (continuous_fst : Continuous (Prod.fst : CollarCylinder A cut × TopCat.I → _))
        change p ∈ frontier (Prod.fst ⁻¹'
          {z : CollarCylinder A cut | (z.1.2.down : ℝ) < cut}) at hp
        rw [hc.frontier_eq] at hp
        exact False.elim hp
      · apply Continuous.subtype_mk
        change Continuous (fun p : CollarCylinder A cut × ULift.{u} I ↦
          (p.2.down : ℝ) * (p.1.1.2.down : ℝ))
        fun_prop
      · apply Continuous.subtype_mk
        change Continuous (fun p : CollarCylinder A cut × ULift.{u} I ↦
          1 - (p.2.down : ℝ) * (1 - (p.1.1.2.down : ℝ)))
        fun_prop

/-- Both half-open pieces strongly retract onto their own endpoint pair. -/
def collarCylinderStrongDeformationRetract (hpos : 0 < cut) (hcut : cut ≤ 1 / 2) :
    Quillen.CylinderStrongDeformationRetract (collarEndpoints A cut hpos) where
  r := collarCylinderRetraction A cut hcut
  retract := by
    classical
    apply ConcreteCategory.hom_ext
    rintro (a | a)
    · change (if (0 : ℝ) < cut then Sum.inl a else Sum.inr a) = Sum.inl a
      simp [hpos]
    · change (if (1 : ℝ) < cut then Sum.inl a else Sum.inr a) = Sum.inr a
      simp [show ¬ (1 : ℝ) < cut by linarith]
  H := collarCylinderDeformation A cut hcut
  H₀ := by
    classical
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    change (z.1.1, ULift.up
      (if (z.1.2.down : ℝ) < cut then (0 : I) * z.1.2.down
       else σ ((0 : I) * σ z.1.2.down))) =
      Quillen.intervalEndpoints A
        (if (z.1.2.down : ℝ) < cut then Sum.inl z.1.1 else Sum.inr z.1.1)
    split_ifs <;> simp only [zero_mul, symm_zero] <;> rfl
  H₁ := by
    classical
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    change (z.1.1, ULift.up
      (if (z.1.2.down : ℝ) < cut then (1 : I) * z.1.2.down
       else σ ((1 : I) * σ z.1.2.down))) = z.1
    simp only [one_mul, symm_symm, ite_self]
  fixed := by
    classical
    apply ConcreteCategory.hom_ext
    rintro ⟨a | a, t⟩ <;> apply Subtype.ext
    · change (a, ULift.up
        (if (0 : ℝ) < cut then t.down * (0 : I) else σ (t.down * σ (0 : I)))) =
        (a, ULift.up (0 : I))
      simp [hpos]
    · change (a, ULift.up
        (if (1 : ℝ) < cut then t.down * (1 : I) else σ (t.down * σ (1 : I)))) =
        (a, ULift.up (1 : I))
      simp [show ¬ (1 : ℝ) < cut by linarith]


private def subtypeAllHomeomorph {X : Type u} [TopologicalSpace X]
    (P : X → Prop) (h : ∀ x, P x) : X ≃ₜ {x // P x} where
  toFun x := ⟨x, h x⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := continuous_subtype_val

variable {A B D : TopCat.{u}} (f₀ f₁ : A ⟶ B)
  {l : A ⊗ TopCat.I ⟶ D} {e : B ⟶ D}
  (sq : IsPushout (Quillen.intervalEndpoints A) (endMap f₀ f₁) l e)

/-- The actual open subspace around the single attached base. -/
abbrev Collar : TopCat.{u} := TopCat.of (collarSet f₀ f₁ sq cut)

/-- The base included into its symmetric-height collar. -/
def collarInclusion (hcut : 0 < cut) : B ⟶ Collar cut f₀ f₁ sq :=
  TopCat.ofHom ⟨fun b ↦ ⟨e b, by
    change height f₀ f₁ sq (e b) < cut
    rwa [height_base]⟩, by fun_prop⟩

/-- The two-piece cylinder included into the actual open collar. -/
def collarCylinderInclusion : CollarCylinder A cut ⟶ Collar cut f₀ f₁ sq :=
  TopCat.ofHom ⟨fun z ↦ ⟨l z.1, by
    change height f₀ f₁ sq (l (z.1.1, z.1.2)) < cut
    rw [height_cylinder]
    exact z.2⟩, by fun_prop⟩

/-- The open collar is the actual pushout attaching both half-open ends to `B`. -/
theorem collar_isPushout (hcut : 0 < cut) :
    IsPushout (collarEndpoints A cut hcut) (endMap f₀ f₁)
      (collarCylinderInclusion cut f₀ f₁ sq) (collarInclusion cut f₀ f₁ sq hcut) := by
  let es : (A ⊕ A) ≃ₜ OpenPushout.source
      (i := Quillen.intervalEndpoints A) (g := l) (collarSet f₀ f₁ sq cut) :=
    subtypeAllHomeomorph _ (by
      rintro (a | a)
      · change height f₀ f₁ sq (l (a, ULift.up 0)) < cut
        simpa only [height_cylinder, endpointDistance_zero] using hcut
      · change height f₀ f₁ sq (l (a, ULift.up 1)) < cut
        simpa only [height_cylinder, endpointDistance_one] using hcut)
  let ec : CollarCylinder A cut ≃ₜ OpenPushout.left
      (g := l) (collarSet f₀ f₁ sq cut) :=
    Homeomorph.setCongr (by
      ext z
      change endpointDistance z.2.down < cut ↔ height f₀ f₁ sq (l (z.1, z.2)) < cut
      rw [height_cylinder])
  let eb : B ≃ₜ OpenPushout.right (j := e) (collarSet f₀ f₁ sq cut) :=
    subtypeAllHomeomorph _ (fun b ↦ by
      change height f₀ f₁ sq (e b) < cut
      rwa [height_base])
  exact (OpenPushout.isPushout sq _ (collar_isOpen f₀ f₁ sq cut)).of_iso'
    (TopCat.isoOfHomeo es) (TopCat.isoOfHomeo ec) (TopCat.isoOfHomeo eb) (Iso.refl _)
    (by ext a; rfl) (by ext a; rfl) (by ext z; rfl) (by ext b; rfl)

/-- The actual open collar strongly deformation retracts onto its single base space. -/
def collarStrongDeformationRetract (hpos : 0 < cut) (hcut : cut ≤ 1 / 2) :
    Quillen.CylinderStrongDeformationRetract (collarInclusion cut f₀ f₁ sq hpos) :=
  (collarCylinderStrongDeformationRetract A cut hpos hcut).pushout
    (collar_isPushout cut f₀ f₁ sq hpos)

/-- The continuous collapse of the collar to the attached base. -/
abbrev collarProjection (hpos : 0 < cut) (hcut : cut ≤ 1 / 2) :
    Collar cut f₀ f₁ sq ⟶ B :=
  (collarStrongDeformationRetract cut f₀ f₁ sq hpos hcut).r

@[simp] theorem collarProjection_base (hpos : 0 < cut) (hcut : cut ≤ 1 / 2) (b : B) :
    collarProjection cut f₀ f₁ sq hpos hcut (collarInclusion cut f₀ f₁ sq hpos b) = b :=
  ConcreteCategory.congr_hom (collarStrongDeformationRetract cut f₀ f₁ sq hpos hcut).retract b

/-- On each component the collar collapses by its own attaching map. -/
theorem collarProjection_cylinder (hpos : 0 < cut) (hcut : cut ≤ 1 / 2)
    (z : CollarCylinder A cut) :
    collarProjection cut f₀ f₁ sq hpos hcut (collarCylinderInclusion cut f₀ f₁ sq z) =
      if (z.1.2.down : ℝ) < cut then f₀ z.1.1 else f₁ z.1.1 := by
  classical
  have h := ConcreteCategory.congr_hom
    ((collarCylinderStrongDeformationRetract A cut hpos hcut).pushout_inl_retraction
      (collar_isPushout cut f₀ f₁ sq hpos)) z
  change _ = endMap f₀ f₁
    (if (z.1.2.down : ℝ) < cut then Sum.inl z.1.1 else Sum.inr z.1.1) at h
  exact h.trans (by split_ifs <;> rfl)

@[simp] theorem collarDeformation_base (hpos : 0 < cut) (hcut : cut ≤ 1 / 2)
    (b : B) (s : TopCat.I) :
    (collarStrongDeformationRetract cut f₀ f₁ sq hpos hcut).H
      (collarInclusion cut f₀ f₁ sq hpos b, s) = collarInclusion cut f₀ f₁ sq hpos b :=
  ConcreteCategory.congr_hom (collarStrongDeformationRetract cut f₀ f₁ sq hpos hcut).fixed (b, s)


/-- The glued collar deformation has the expected formula on both cylinder pieces. -/
theorem collarDeformation_cylinder (hpos : 0 < cut) (hcut : cut ≤ 1 / 2)
    (z : CollarCylinder A cut) (s : TopCat.I) :
    ((collarStrongDeformationRetract cut f₀ f₁ sq hpos hcut).H
      (collarCylinderInclusion cut f₀ f₁ sq z, s)).1 =
      l (z.1.1, ULift.up (if (z.1.2.down : ℝ) < cut then s.down * z.1.2.down
        else σ (s.down * σ z.1.2.down))) :=
  congrArg Subtype.val (ConcreteCategory.congr_hom
    ((collarCylinderStrongDeformationRetract A cut hpos hcut).pushout_inl_homotopy
      (collar_isPushout cut f₀ f₁ sq hpos)) (z, s))

/-- Any collar base map independent of height on each cylinder component is
preserved throughout the actual deformation. -/
theorem collarDeformation_over {T : TopCat.{u}} (hpos : 0 < cut) (hcut : cut ≤ 1 / 2)
    (p : Collar cut f₀ f₁ sq ⟶ T) (a : A ⟶ T)
    (hp : ∀ z : CollarCylinder A cut, p (collarCylinderInclusion cut f₀ f₁ sq z) = a z.1.1) :
    (collarStrongDeformationRetract cut f₀ f₁ sq hpos hcut).H ≫ p =
      fst (Collar cut f₀ f₁ sq) TopCat.I ≫ p := by
  apply (collarCylinderStrongDeformationRetract A cut hpos hcut).pushout_homotopy_over
    (collar_isPushout cut f₀ f₁ sq hpos)
  apply ConcreteCategory.hom_ext
  rintro ⟨z, s⟩
  exact (hp ((collarCylinderStrongDeformationRetract A cut hpos hcut).H (z, s))).trans
    (hp z).symm

/-- The collar projection is strictly over any such height-independent base map. -/
theorem collarProjection_over {T : TopCat.{u}} (hpos : 0 < cut) (hcut : cut ≤ 1 / 2)
    (p : Collar cut f₀ f₁ sq ⟶ T) (a : A ⟶ T)
    (hp : ∀ z : CollarCylinder A cut, p (collarCylinderInclusion cut f₀ f₁ sq z) = a z.1.1) :
    collarProjection cut f₀ f₁ sq hpos hcut ≫ collarInclusion cut f₀ f₁ sq hpos ≫ p = p := by
  have hh := congrArg (fun k ↦ TopCat.ι₀ ≫ k)
    (collarDeformation_over cut f₀ f₁ sq hpos hcut p a hp)
  simpa only [← Category.assoc, (collarStrongDeformationRetract cut f₀ f₁ sq hpos hcut).H₀,
    TopCat.ι₀_fst, Category.id_comp] using hh

end Quillen.CylinderAttachment
