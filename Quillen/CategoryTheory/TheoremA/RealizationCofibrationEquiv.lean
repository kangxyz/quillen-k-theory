/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.TheoremA.RealizationGluing
public import Mathlib.Topology.Homotopy.TopCat.Basic

/-!
# Strictifying a homotopy inverse along a cofibration

The homotopy extension property turns an actual homotopy inverse into a
strict retraction. This is the first step toward relative deformation
retractions and the general homotopy gluing theorem.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u

namespace Quillen.TheoremA

/-- HEP in categorical cylinder coordinates also gives extensions in ordinary
continuous-map coordinates, including an arbitrary compact-open target. -/
theorem homotopyExtensionProperty_continuous {A B : TopCat.{u}} {i : A ⟶ B}
    (hi : homotopyExtensionProperty i) (Z : TopCat.{u})
    (f : C(B, Z)) (H : C(unitInterval × A, Z))
    (hzero : ∀ a, H (0, a) = f (i a)) :
    ∃ K : C(unitInterval × B, Z), (∀ b, K (0, b) = f b) ∧
      ∀ t a, K (t, i a) = H (t, a) := by
  let H' : A ⊗ TopCat.I ⟶ Z := TopCat.ofHom
    ⟨fun p ↦ H (p.2.down, p.1), H.continuous.comp
      ((continuous_uliftDown.comp continuous_snd).prodMk continuous_fst)⟩
  obtain ⟨K, hK₀, hK⟩ := hi Z (TopCat.ofHom f) H' (by ext a; exact hzero a)
  refine ⟨⟨fun p ↦ K (p.2, ULift.up p.1), K.hom.continuous.comp
    (continuous_snd.prodMk (continuous_uliftUp.comp continuous_fst))⟩, ?_, ?_⟩
  · intro b
    exact ConcreteCategory.congr_hom hK₀ b
  · intro t a
    exact ConcreteCategory.congr_hom hK (a, ULift.up t)

/-- A cofibration which is a homotopy equivalence has a strict continuous
retraction which is still a homotopy inverse. Both the forward map and the
strict retraction equation refer to the specified map `i`. -/
theorem homotopyExtensionProperty_exists_retraction {A B : TopCat.{u}}
    {i : A ⟶ B} (hi : homotopyExtensionProperty i)
    (e : ContinuousMap.HomotopyEquiv A B) (he : e.toFun = i.hom) :
    ∃ r : B ⟶ A, i ≫ r = 𝟙 A ∧
      Nonempty (TopCat.Homotopy (r ≫ i) (𝟙 B)) := by
  let r₀ : B ⟶ A := TopCat.ofHom e.invFun
  have hleft : TopCat.Homotopy (i ≫ r₀) (𝟙 A) := by
    change (e.invFun.comp i.hom).Homotopy (ContinuousMap.id A)
    rw [← he]
    exact e.left_inv.some
  obtain ⟨K, hK₀, hK⟩ := hi A r₀ hleft.h hleft.ι₀_h
  let r : B ⟶ A := TopCat.ι₁ ≫ K
  have hir : i ≫ r = 𝟙 A := by
    dsimp [r]
    rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc, hK, hleft.ι₁_h]
  have hr : TopCat.Homotopy r₀ r := homotopyOfCylinder K hK₀ rfl
  have hright : TopCat.Homotopy (r₀ ≫ i) (𝟙 B) := by
    change (i.hom.comp e.invFun).Homotopy (ContinuousMap.id B)
    rw [← he]
    exact e.right_inv.some
  refine ⟨r, hir, ⟨?_⟩⟩
  exact ((TopCat.Homotopy.refl i).comp hr.symm).trans hright

/-- The interval parameter which traverses a path backwards and then forwards. -/
def backtrackTime (t : unitInterval) : unitInterval :=
  ⟨|2 * (t : ℝ) - 1|, abs_nonneg _, by
    rw [abs_le]
    constructor <;> linarith [t.2.1, t.2.2]⟩

@[fun_prop]
theorem continuous_backtrackTime : Continuous backtrackTime := by
  unfold backtrackTime
  fun_prop

@[simp]
theorem backtrackTime_zero : backtrackTime 0 = 1 := by
  apply Subtype.ext
  norm_num [backtrackTime]

@[simp]
theorem backtrackTime_one : backtrackTime 1 = 1 := by
  apply Subtype.ext
  norm_num [backtrackTime]

/-- Shrink the backwards-and-forwards traversal to its common endpoint. -/
def shrinkBacktrackTime (s t : unitInterval) : unitInterval :=
  ⟨(s : ℝ) + (1 - s) * backtrackTime t, by
    constructor
    · exact add_nonneg s.2.1
        (mul_nonneg (sub_nonneg.mpr s.2.2) (backtrackTime t).2.1)
    · nlinarith [(backtrackTime t).2.1, (backtrackTime t).2.2, s.2.1, s.2.2]⟩

@[fun_prop]
theorem continuous_shrinkBacktrackTime :
    Continuous (fun p : unitInterval × unitInterval ↦ shrinkBacktrackTime p.1 p.2) := by
  unfold shrinkBacktrackTime
  fun_prop

@[simp]
theorem shrinkBacktrackTime_zero (t : unitInterval) : shrinkBacktrackTime 0 t = backtrackTime t :=
  by
  apply Subtype.ext
  simp [shrinkBacktrackTime]

@[simp]
theorem shrinkBacktrackTime_one (t : unitInterval) : shrinkBacktrackTime 1 t = 1 := by
  apply Subtype.ext
  simp [shrinkBacktrackTime]

@[simp]
theorem shrinkBacktrackTime_left (s : unitInterval) : shrinkBacktrackTime s 0 = 1 := by
  apply Subtype.ext
  simp [shrinkBacktrackTime]

@[simp]
theorem shrinkBacktrackTime_right (s : unitInterval) : shrinkBacktrackTime s 1 = 1 := by
  apply Subtype.ext
  simp [shrinkBacktrackTime]

/-- A homotopy starting at a strict retraction can be modified so that its
restriction is a backwards-and-forwards loop with a canonical contraction. -/
def retractionBacktrackHomotopy {A B : TopCat.{u}} {i : A ⟶ B} {r : B ⟶ A}
    (hir : i ≫ r = 𝟙 A) (F : TopCat.Homotopy (r ≫ i) (𝟙 B)) :
    TopCat.Homotopy (r ≫ i) (𝟙 B) := by
  let f := (r ≫ i).hom
  have hff : f.comp f = f := by
    change ((r ≫ i) ≫ (r ≫ i)).hom = (r ≫ i).hom
    rw [Category.assoc, ← Category.assoc i r i, hir]
    simp
  let L : f.Homotopy f :=
    (F.compContinuousMap f).cast hff (by ext x; rfl)
  exact L.symm.trans F

/-- On the retract the modified homotopy is the explicit backtracking loop. -/
theorem retractionBacktrackHomotopy_restrict {A B : TopCat.{u}} {i : A ⟶ B} {r : B ⟶ A}
    (hir : i ≫ r = 𝟙 A) (F : TopCat.Homotopy (r ≫ i) (𝟙 B))
    (t : unitInterval) (a : A) :
    retractionBacktrackHomotopy hir F (t, i a) = F (backtrackTime t, i a) := by
  have hri : r (i a) = a := ConcreteCategory.congr_hom hir a
  simp only [retractionBacktrackHomotopy, ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · change F (unitInterval.symm ⟨2 * (t : ℝ), _⟩, i (r (i a))) = _
    rw [hri]
    congr 2
    apply Subtype.ext
    dsimp [backtrackTime, unitInterval.symm]
    rw [abs_of_nonpos (by linarith)]
    ring
  · change F (⟨2 * (t : ℝ) - 1, _⟩, i a) = _
    congr 2
    apply Subtype.ext
    dsimp [backtrackTime]
    rw [abs_of_nonneg (by linarith)]

/-- The homotopy extension property makes a deformation retraction relative
by extending a canonical contraction of the restriction's backtracking loop
into the compact-open path space. -/
theorem homotopyExtensionProperty_relative_retraction {A B : TopCat.{u}}
    {i : A ⟶ B} {r : B ⟶ A} (hi : homotopyExtensionProperty i)
    (hir : i ≫ r = 𝟙 A) (F : TopCat.Homotopy (r ≫ i) (𝟙 B)) :
    ∃ K : TopCat.Homotopy (r ≫ i) (𝟙 B), ∀ t a, K (t, i a) = i a := by
  let f := (r ≫ i).hom
  have hfix : ∀ a, f (i a) = i a := by
    intro a
    exact congrArg i (ConcreteCategory.congr_hom hir a)
  let K := retractionBacktrackHomotopy hir F
  let Kc : C(B, C(unitInterval, B)) :=
    (K.toContinuousMap.comp ContinuousMap.prodSwap).curry
  let G : C((unitInterval × A) × unitInterval, B) :=
    ⟨fun p ↦ F (shrinkBacktrackTime p.1.1 p.2, i p.1.2),
      F.continuous.comp ((continuous_shrinkBacktrackTime.comp
        (continuous_fst.fst.prodMk continuous_snd)).prodMk
        (i.hom.continuous.comp continuous_fst.snd))⟩
  have hG₀ : ∀ a, G.curry (0, a) = Kc (i a) := by
    intro a
    ext t
    change F (shrinkBacktrackTime 0 t, i a) = K (t, i a)
    rw [shrinkBacktrackTime_zero]
    exact (retractionBacktrackHomotopy_restrict hir F t a).symm
  obtain ⟨Q, hQ₀, hQ⟩ := homotopyExtensionProperty_continuous hi
    (TopCat.of C(unitInterval, B)) Kc G.curry hG₀
  let e₀ : C(B, B) := ⟨fun b ↦ Q (1, b) 0, by fun_prop⟩
  let e₁ : C(B, B) := ⟨fun b ↦ Q (1, b) 1, by fun_prop⟩
  let L₀ : f.Homotopy e₀ := {
    toFun := fun p ↦ Q p 0
    continuous_toFun := by fun_prop
    map_zero_left := fun b ↦ by
      rw [hQ₀]
      exact K.map_zero_left b
    map_one_left := fun _ ↦ rfl }
  let L₁ : e₀.Homotopy e₁ := {
    toFun := fun p ↦ Q (1, p.2) p.1
    continuous_toFun := by fun_prop
    map_zero_left := fun _ ↦ rfl
    map_one_left := fun _ ↦ rfl }
  let L₂ : e₁.Homotopy (ContinuousMap.id B) := {
    toFun := fun p ↦ Q (unitInterval.symm p.1, p.2) 1
    continuous_toFun := by fun_prop
    map_zero_left := fun b ↦ by simp [e₁]
    map_one_left := fun b ↦ by
      rw [unitInterval.symm_one, hQ₀]
      exact K.map_one_left b }
  have hL₀ : ∀ t a, L₀ (t, i a) = i a := by
    intro t a
    change Q (t, i a) 0 = i a
    rw [hQ]
    change F (shrinkBacktrackTime t 0, i a) = i a
    simp
  have hL₁ : ∀ t a, L₁ (t, i a) = i a := by
    intro t a
    change Q (1, i a) t = i a
    rw [hQ]
    change F (shrinkBacktrackTime 1 t, i a) = i a
    simp
  have hL₂ : ∀ t a, L₂ (t, i a) = i a := by
    intro t a
    change Q (unitInterval.symm t, i a) 1 = i a
    rw [hQ]
    change F (shrinkBacktrackTime (unitInterval.symm t) 1, i a) = i a
    simp
  let R₀ : f.HomotopyRel e₀ (Set.range i) := {
    toHomotopy := L₀
    prop' := by rintro t _ ⟨a, rfl⟩; exact (hL₀ t a).trans (hfix a).symm }
  let R₁ : e₀.HomotopyRel e₁ (Set.range i) := {
    toHomotopy := L₁
    prop' := by
      rintro t _ ⟨a, rfl⟩
      exact (hL₁ t a).trans (hL₀ 1 a).symm }
  let R₂ : e₁.HomotopyRel (ContinuousMap.id B) (Set.range i) := {
    toHomotopy := L₂
    prop' := by
      rintro t _ ⟨a, rfl⟩
      exact (hL₂ t a).trans (hL₁ 1 a).symm }
  let R := (R₀.trans R₁).trans R₂
  refine ⟨R.toHomotopy, fun t a ↦ ?_⟩
  exact (R.prop t (i a) ⟨a, rfl⟩).trans (hfix a)

/-- A cofibration which is a homotopy equivalence is an actual strong
 deformation retract, with no relative homotopy assumed in the hypotheses. -/
theorem homotopyExtensionProperty_strongDeformationRetract {A B : TopCat.{u}}
    {i : A ⟶ B} (hi : homotopyExtensionProperty i)
    (e : ContinuousMap.HomotopyEquiv A B) (he : e.toFun = i.hom) :
    Nonempty (CylinderStrongDeformationRetract i) := by
  obtain ⟨r, hir, ⟨F⟩⟩ := homotopyExtensionProperty_exists_retraction hi e he
  obtain ⟨K, hK⟩ := homotopyExtensionProperty_relative_retraction hi hir F
  refine ⟨⟨r, hir, K.h, K.ι₀_h, K.ι₁_h, ?_⟩⟩
  ext ⟨a, t⟩
  exact hK (TopCat.I.homeomorph t) a

/-- The canonical cobase change of a homotopy-equivalence cofibration is
an actual homotopy equivalence. -/
def pushoutHomotopyEquivOfCofibration {A B C D : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) (hi : homotopyExtensionProperty i)
    (e : ContinuousMap.HomotopyEquiv A B) (he : e.toFun = i.hom) :
    ContinuousMap.HomotopyEquiv C D :=
  ((homotopyExtensionProperty_strongDeformationRetract hi e he).some.pushout sq).toHomotopyEquiv

@[simp]
theorem pushoutHomotopyEquivOfCofibration_toFun {A B C D : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) (hi : homotopyExtensionProperty i)
    (e : ContinuousMap.HomotopyEquiv A B) (he : e.toFun = i.hom) :
    (pushoutHomotopyEquivOfCofibration sq hi e he).toFun = j.hom := rfl

end Quillen.TheoremA
