/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

import Quillen.CategoryTheory.TheoremB.MappingCylinderSourceCollar
import Quillen.CategoryTheory.TheoremB.FiberwiseBridgeTargetCollar

/-!
# Actual source-collar charts of a two-cylinder bridge

The two open charts consist of one entire cylinder and the product source
collar of the other. Their intersection is the pushout of the two source
collars. All three squares are restrictions of the original topological
pushout, and the local strong deformations keep the original base fixed.
No weakness or lifting hypothesis is used in this geometry.
-/
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.TheoremB.FiberwiseBridgeSourceCharts

private def allSubtypeHomeomorph {X : Type u} [TopologicalSpace X]
    (P : X → Prop) (hP : ∀ x, P x) : X ≃ₜ {x // P x} where
  toFun x := ⟨x, hP x⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := continuous_subtype_val

variable {A B C M N Z T : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
  {lM : A ⊗ TopCat.I ⟶ M} {cM : B ⟶ M}
  {lN : A ⊗ TopCat.I ⟶ N} {cN : C ⟶ N}
  (sqM : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f lM cM)
  {m : M ⟶ Z} {n : N ⟶ Z}
  (sq : IsPushout (TopCat.ι₀ ≫ lM) (TopCat.ι₀ ≫ lN) m n)
  (cut : I) (hcut : 0 < cut)

/-- The chart containing the whole right cylinder and the left source collar. -/
def sideSet : Set Z := {z | FiberwiseBridgeTargetCollar.height sqM sq z < cut}

theorem side_isOpen : IsOpen (sideSet sqM sq cut) :=
  isOpen_lt (FiberwiseBridgeTargetCollar.height sqM sq).continuous continuous_const

abbrev Side : TopCat.{u} := TopCat.of (sideSet sqM sq cut)

def sideInclusion : Side sqM sq cut ⟶ Z :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem side_preimage_left :
    m ⁻¹' sideSet sqM sq cut = MappingCylinderSourceCollar.collarSet sqM cut := by
  ext x
  change FiberwiseBridgeTargetCollar.height sqM sq (m x) < cut ↔ _
  rw [FiberwiseBridgeTargetCollar.height_left]
  rfl

include hcut in
@[simp] theorem side_preimage_right : n ⁻¹' sideSet sqM sq cut = Set.univ := by
  ext x
  change FiberwiseBridgeTargetCollar.height sqM sq (n x) < cut ↔ True
  rw [FiberwiseBridgeTargetCollar.height_right]
  exact iff_true_intro hcut

/-- The left collar enters the original bridge chart with its unchanged point. -/
def sideCollar : MappingCylinderSourceCollar.Collar sqM cut ⟶ Side sqM sq cut :=
  TopCat.ofHom ⟨fun x ↦ ⟨m x.val, by
    change FiberwiseBridgeTargetCollar.height sqM sq (m x.val) < cut
    rw [FiberwiseBridgeTargetCollar.height_left]
    exact x.property⟩, by fun_prop⟩

/-- The whole right cylinder enters the original bridge chart. -/
def sideEnd : N ⟶ Side sqM sq cut := TopCat.ofHom ⟨fun x ↦ ⟨n x, by
    change FiberwiseBridgeTargetCollar.height sqM sq (n x) < cut
    rw [FiberwiseBridgeTargetCollar.height_right]
    exact hcut⟩, by fun_prop⟩

@[simp] theorem sideCollar_val (x : MappingCylinderSourceCollar.Collar sqM cut) :
    (sideCollar sqM sq cut x).val = m x.val := rfl
@[simp] theorem sideEnd_val (x : N) : (sideEnd sqM sq cut hcut x).val = n x := rfl

/-- This square is the actual open restriction of the given bridge pushout. -/
theorem side_isPushout :
    IsPushout (MappingCylinderSourceCollar.source sqM cut hcut) (TopCat.ι₀ ≫ lN)
      (sideCollar sqM sq cut) (sideEnd sqM sq cut hcut) := by
  let W := sideSet sqM sq cut
  let es : A ≃ₜ OpenPushout.source (i := TopCat.ι₀ ≫ lM) (g := m) W :=
    allSubtypeHomeomorph _ (fun a ↦ by
      change FiberwiseBridgeTargetCollar.height sqM sq (m ((TopCat.ι₀ ≫ lM) a)) < cut
      rw [FiberwiseBridgeTargetCollar.height_left, MappingCylinderTargetCollar.height_start]
      exact hcut)
  let el : MappingCylinderSourceCollar.Collar sqM cut ≃ₜ OpenPushout.left (g := m) W :=
    Homeomorph.setCongr (side_preimage_left sqM sq cut).symm
  let er : N ≃ₜ OpenPushout.right (j := n) W :=
    allSubtypeHomeomorph _ (fun x ↦ by
      change FiberwiseBridgeTargetCollar.height sqM sq (n x) < cut
      rw [FiberwiseBridgeTargetCollar.height_right]
      exact hcut)
  exact (OpenPushout.isPushout sq W (side_isOpen sqM sq cut)).of_iso'
    (TopCat.isoOfHomeo es) (TopCat.isoOfHomeo el) (TopCat.isoOfHomeo er) (Iso.refl _)
    (by ext a; rfl) (by ext a; rfl) (by ext x; rfl) (by ext x; rfl)

/-- The chart genuinely retracts to its unchanged entire-cylinder end. -/
def sideStrongDeformationRetract :
    TheoremA.CylinderStrongDeformationRetract (sideEnd sqM sq cut hcut) :=
  (MappingCylinderSourceCollar.strongDeformationRetract sqM cut hcut).pushout
    (side_isPushout sqM sq cut hcut)

/-- Pushout extension retains the entire over-base deformation. -/
theorem sideStrongDeformationRetract_over (p : Z ⟶ T)
    (hM : (MappingCylinderSourceCollar.strongDeformationRetract sqM cut hcut).H ≫
      MappingCylinderSourceCollar.inclusion sqM cut ≫ m ≫ p =
      fst (MappingCylinderSourceCollar.Collar sqM cut) TopCat.I ≫
        MappingCylinderSourceCollar.inclusion sqM cut ≫ m ≫ p) :
    (sideStrongDeformationRetract sqM sq cut hcut).H ≫ sideInclusion sqM sq cut ≫ p =
      fst (Side sqM sq cut) TopCat.I ≫ sideInclusion sqM sq cut ≫ p := by
  apply (MappingCylinderSourceCollar.strongDeformationRetract sqM cut hcut).pushout_homotopy_over
    (side_isPushout sqM sq cut hcut)
  exact hM

/-- The source chart for the left map is its literal product collar. -/
def sideSourceHomeomorph : {x : M // m x ∈ sideSet sqM sq cut} ≃ₜ
    MappingCylinderSourceCollar.Collar sqM cut :=
  Homeomorph.setCongr (side_preimage_left sqM sq cut)

/-- The source chart for the right map is its entire original cylinder. -/
def sideEndSourceHomeomorph : {x : N // n x ∈ sideSet sqM sq cut} ≃ₜ N :=
  (allSubtypeHomeomorph _ (fun x ↦ by
    change FiberwiseBridgeTargetCollar.height sqM sq (n x) < cut
    rw [FiberwiseBridgeTargetCollar.height_right]
    exact hcut)).symm

variable (sqN : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) g lN cN)

include hcut in
/-- The source neighborhoods of the two cylinders cover the whole bridge. -/
theorem side_cover : sideSet sqM sq cut ∪ sideSet sqN sq.flip cut = Set.univ := by
  ext z
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) z with ⟨x, hx⟩ | ⟨y, hy⟩
  · change m x = z at hx
    rw [← hx]
    exact Or.inr (sideEnd sqN sq.flip cut hcut x).property
  · change n y = z at hy
    rw [← hy]
    exact Or.inl (sideEnd sqM sq cut hcut y).property

/-- The overlap consists of precisely the two source collars glued together. -/
def intersectionSet : Set Z := sideSet sqM sq cut ∩ sideSet sqN sq.flip cut

abbrev Intersection : TopCat.{u} := TopCat.of (intersectionSet sqM sq cut sqN)

def intersectionInclusion : Intersection sqM sq cut sqN ⟶ Z :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem intersection_isOpen : IsOpen (intersectionSet sqM sq cut sqN) :=
  (side_isOpen sqM sq cut).inter (side_isOpen sqN sq.flip cut)

include hcut in
@[simp] theorem intersection_preimage_left :
    m ⁻¹' intersectionSet sqM sq cut sqN = MappingCylinderSourceCollar.collarSet sqM cut := by
  rw [intersectionSet, Set.preimage_inter, side_preimage_left,
    side_preimage_right sqN sq.flip cut hcut, Set.inter_univ]

include hcut in
@[simp] theorem intersection_preimage_right :
    n ⁻¹' intersectionSet sqM sq cut sqN = MappingCylinderSourceCollar.collarSet sqN cut := by
  rw [intersectionSet, Set.preimage_inter, side_preimage_right sqM sq cut hcut,
    side_preimage_left, Set.univ_inter]

def intersectionLeft : MappingCylinderSourceCollar.Collar sqM cut ⟶ Intersection sqM sq cut sqN :=
  TopCat.ofHom ⟨fun x ↦ ⟨m x.val, by
    change x.val ∈ m ⁻¹' intersectionSet sqM sq cut sqN
    rw [intersection_preimage_left sqM sq cut hcut sqN]
    exact x.property⟩,
    by fun_prop⟩

def intersectionRight : MappingCylinderSourceCollar.Collar sqN cut ⟶ Intersection sqM sq cut sqN :=
  TopCat.ofHom ⟨fun x ↦ ⟨n x.val, by
    change x.val ∈ n ⁻¹' intersectionSet sqM sq cut sqN
    rw [intersection_preimage_right sqM sq cut hcut sqN]
    exact x.property⟩,
    by fun_prop⟩

@[simp] theorem intersectionLeft_val (x : MappingCylinderSourceCollar.Collar sqM cut) :
    (intersectionLeft sqM sq cut hcut sqN x).val = m x.val := rfl
@[simp] theorem intersectionRight_val (x : MappingCylinderSourceCollar.Collar sqN cut) :
    (intersectionRight sqM sq cut hcut sqN x).val = n x.val := rfl

/-- All four corners and maps are transported from the original open restriction. -/
theorem intersection_isPushout :
    IsPushout (MappingCylinderSourceCollar.source sqM cut hcut)
      (MappingCylinderSourceCollar.source sqN cut hcut)
      (intersectionLeft sqM sq cut hcut sqN) (intersectionRight sqM sq cut hcut sqN) := by
  let W := intersectionSet sqM sq cut sqN
  let es : A ≃ₜ OpenPushout.source (i := TopCat.ι₀ ≫ lM) (g := m) W :=
    allSubtypeHomeomorph _ (fun a ↦ by
      change (TopCat.ι₀ ≫ lM) a ∈ m ⁻¹' intersectionSet sqM sq cut sqN
      rw [intersection_preimage_left sqM sq cut hcut sqN]
      exact (MappingCylinderSourceCollar.source sqM cut hcut a).property)
  let el : MappingCylinderSourceCollar.Collar sqM cut ≃ₜ OpenPushout.left (g := m) W :=
    Homeomorph.setCongr (intersection_preimage_left sqM sq cut hcut sqN).symm
  let er : MappingCylinderSourceCollar.Collar sqN cut ≃ₜ OpenPushout.right (j := n) W :=
    Homeomorph.setCongr (intersection_preimage_right sqM sq cut hcut sqN).symm
  exact (OpenPushout.isPushout sq W (intersection_isOpen sqM sq cut sqN)).of_iso'
    (TopCat.isoOfHomeo es) (TopCat.isoOfHomeo el) (TopCat.isoOfHomeo er) (Iso.refl _)
    (by ext a; rfl) (by ext a; rfl) (by ext x; rfl) (by ext x; rfl)

/-- The overlap strongly deforms onto its actual left source collar. -/
def intersectionStrongDeformationRetract :
    TheoremA.CylinderStrongDeformationRetract (intersectionLeft sqM sq cut hcut sqN) :=
  (MappingCylinderSourceCollar.strongDeformationRetract sqN cut hcut).pushout
    (intersection_isPushout sqM sq cut hcut sqN).flip

/-- The entire overlap deformation preserves a supplied original base map. -/
theorem intersectionStrongDeformationRetract_over (p : Z ⟶ T)
    (hN : (MappingCylinderSourceCollar.strongDeformationRetract sqN cut hcut).H ≫
      MappingCylinderSourceCollar.inclusion sqN cut ≫ n ≫ p =
      fst (MappingCylinderSourceCollar.Collar sqN cut) TopCat.I ≫
        MappingCylinderSourceCollar.inclusion sqN cut ≫ n ≫ p) :
    (intersectionStrongDeformationRetract sqM sq cut hcut sqN).H ≫
      intersectionInclusion sqM sq cut sqN ≫ p =
      fst (Intersection sqM sq cut sqN) TopCat.I ≫ intersectionInclusion sqM sq cut sqN ≫ p := by
  apply (MappingCylinderSourceCollar.strongDeformationRetract sqN cut hcut).pushout_homotopy_over
    (intersection_isPushout sqM sq cut hcut sqN).flip
  exact hN

/-- The left cylinder's actual source over the overlap is its source collar. -/
def intersectionSourceHomeomorph : {x : M // m x ∈ intersectionSet sqM sq cut sqN} ≃ₜ
    MappingCylinderSourceCollar.Collar sqM cut :=
  Homeomorph.setCongr (intersection_preimage_left sqM sq cut hcut sqN)

end Quillen.TheoremB.FiberwiseBridgeSourceCharts
