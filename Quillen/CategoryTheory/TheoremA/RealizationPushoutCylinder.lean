/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.TheoremA.RealizationPushoutRelative

/-!
# The mapping-cylinder comparison for cofibrant attaching maps

The ordinary pushout of a span with an HEP leg is homotopy equivalent to
its mapping-cylinder replacement. The equivalence is the canonical collapse.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval

universe u

namespace Quillen.TheoremA

/-- Move an interval coordinate linearly toward its terminal endpoint. -/
def intervalSlide (s t : unitInterval) : unitInterval :=
  unitInterval.symm ((unitInterval.symm s) * (unitInterval.symm t))

@[fun_prop]
theorem continuous_intervalSlide :
    Continuous (fun p : unitInterval × unitInterval ↦ intervalSlide p.1 p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : unitInterval × unitInterval ↦
    1 - ((1 - (p.1 : ℝ)) * (1 - (p.2 : ℝ))))
  fun_prop

@[simp] theorem intervalSlide_zero (t : unitInterval) : intervalSlide 0 t = t := by
  simp [intervalSlide]
@[simp] theorem intervalSlide_one (t : unitInterval) : intervalSlide 1 t = 1 := by
  simp [intervalSlide]
@[simp] theorem intervalSlide_left (s : unitInterval) : intervalSlide s 0 = s := by
  simp [intervalSlide]
@[simp] theorem intervalSlide_right (s : unitInterval) : intervalSlide s 1 = 1 := by
  simp [intervalSlide]

/-- The terminal endpoint is a strong deformation retract of the cylinder. -/
def cylinderEndpointStrongDeformationRetract (A : TopCat.{u}) :
    CylinderStrongDeformationRetract (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) where
  r := fst A TopCat.I
  retract := TopCat.ι₁_fst A
  H := TopCat.ofHom
    ⟨fun p ↦ (p.1.1, ULift.up (intervalSlide (unitInterval.symm p.2.down) p.1.2.down)),
      continuous_fst.fst.prodMk (continuous_uliftUp.comp
        (continuous_intervalSlide.comp ((unitInterval.continuous_symm.comp
          (continuous_uliftDown.comp continuous_snd)).prodMk
          (continuous_uliftDown.comp continuous_fst.snd))))⟩
  H₀ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    change (a, ULift.up (intervalSlide (unitInterval.symm 0) t.down)) = (a, 1)
    simp only [unitInterval.symm_zero, intervalSlide_one]
    rfl
  H₁ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    change (a, ULift.up (intervalSlide (unitInterval.symm 1) t.down)) = (a, t)
    simp only [unitInterval.symm_one, intervalSlide_zero]
    rfl
  fixed := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    change (a, ULift.up (intervalSlide (unitInterval.symm t.down) 1)) = (a, 1)
    simp only [intervalSlide_right]
    rfl

/-- The usual mapping-cylinder projection, expressed using its actual
pushout universal property. -/
def mappingCylinderProjection {A C M : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) : M ⟶ C :=
  sq.desc (fst A TopCat.I ≫ f) (𝟙 C) (by simp)

@[reassoc (attr := simp)]
theorem mappingCylinderProjection_cylinder {A C M : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) :
    l ≫ mappingCylinderProjection sq = fst A TopCat.I ≫ f := sq.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem mappingCylinderProjection_target {A C M : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) :
    c ≫ mappingCylinderProjection sq = 𝟙 C := sq.inr_desc _ _ _

@[reassoc]
theorem mappingCylinderProjection_start {A C M : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) :
    TopCat.ι₀ ≫ l ≫ mappingCylinderProjection sq = f := by simp

/-- The mapping-cylinder target inclusion is always an actual strong
 deformation retract. -/
def mappingCylinderTargetStrongDeformationRetract {A C M : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) :
    CylinderStrongDeformationRetract c :=
  (cylinderEndpointStrongDeformationRetract A).pushout sq

/-- The canonical collapse from a mapping-cylinder replacement of an
attaching pushout to the ordinary pushout is an actual homotopy equivalence
whenever the attaching map has HEP. -/
def mappingCylinderPushoutCollapseHomotopyEquiv
    {A B C M Q D : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    {b : B ⟶ Q} {m : M ⟶ Q} {g : B ⟶ D} {j : C ⟶ D}
    (sqM : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c)
    (sqQ : IsPushout i (TopCat.ι₀ ≫ l) b m)
    (sqD : IsPushout i f g j) (hi : homotopyExtensionProperty i) :
    ContinuousMap.HomotopyEquiv Q D := by
  let p := mappingCylinderProjection sqM
  have hq : i ≫ g = (TopCat.ι₀ ≫ l) ≫ p ≫ j := by
    rw [Category.assoc, mappingCylinderProjection_start_assoc, sqD.w]
  let q := sqQ.desc g (p ≫ j) hq
  have hbq : b ≫ q = g := sqQ.inl_desc _ _ _
  have hmq : m ≫ q = p ≫ j := sqQ.inr_desc _ _ _
  have hstart : TopCat.ι₀ ≫ l ≫ m = i ≫ b := sqQ.w.symm
  let hK := hi Q b (l ≫ m) hstart
  let K := hK.choose
  have hK₀ : TopCat.ι₀ ≫ K = b := hK.choose_spec.1
  have hK : (i ▷ TopCat.I) ≫ K = l ≫ m := hK.choose_spec.2
  have hs : i ≫ TopCat.ι₁ ≫ K = f ≫ c ≫ m := by
    rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc, hK,
      ← Category.assoc, sqM.w, Category.assoc]
  let s := sqD.desc (TopCat.ι₁ ≫ K) (c ≫ m) hs
  have hgs : g ≫ s = TopCat.ι₁ ≫ K := sqD.inl_desc _ _ _
  have hjs : j ≫ s = c ≫ m := sqD.inr_desc _ _ _
  let HK : TopCat.Homotopy b (g ≫ s) := homotopyOfCylinder K hK₀ hgs.symm
  let HR : TopCat.Homotopy (g ≫ 𝟙 D) (g ≫ s ≫ q) :=
    ((TopCat.Homotopy.refl q).comp HK).cast
      (by ext x; exact ConcreteCategory.congr_hom hbq x) rfl
  have hHR : ∀ t a, HR (t, i a) = (𝟙 D) (g (i a)) := by
    intro t a
    change q (K (i a, ULift.up t)) = g (i a)
    have hk := ConcreteCategory.congr_hom hK (a, ULift.up t)
    change K (i a, ULift.up t) = m (l (a, ULift.up t)) at hk
    rw [hk]
    have hm := ConcreteCategory.congr_hom hmq (l (a, ULift.up t))
    change q (m (l (a, ULift.up t))) = j (p (l (a, ULift.up t))) at hm
    rw [hm]
    have hp := ConcreteCategory.congr_hom (mappingCylinderProjection_cylinder sqM)
      (a, ULift.up t)
    change p (l (a, ULift.up t)) = f a at hp
    rw [hp]
    exact (ConcreteCategory.congr_hom sqD.w a).symm
  have hjR : j ≫ 𝟙 D = j ≫ s ≫ q := by
    rw [← Category.assoc j s q, hjs, Category.assoc, hmq,
      ← Category.assoc c p j, mappingCylinderProjection_target, Category.id_comp,
      Category.comp_id]
  let right : TopCat.Homotopy (𝟙 D) (s ≫ q) := pushoutHomotopyOfRelative sqD HR hHR hjR
  let sqMI := sqM.map (tensorRight TopCat.I)
  let U : (A ⊗ TopCat.I) ⊗ TopCat.I ⟶ Q := TopCat.ofHom
    ⟨fun z ↦ m (l (z.1.1, ULift.up (intervalSlide z.2.down z.1.2.down))),
      m.hom.continuous.comp (l.hom.continuous.comp
        (continuous_fst.fst.prodMk (continuous_uliftUp.comp
          (continuous_intervalSlide.comp ((continuous_uliftDown.comp continuous_snd).prodMk
            (continuous_uliftDown.comp continuous_fst.snd))))))⟩
  have hwU : (TopCat.ι₁ ▷ TopCat.I) ≫ U =
      (f ▷ TopCat.I) ≫ fst C TopCat.I ≫ c ≫ m := by
    ext ⟨a, t⟩
    change m (l (a, ULift.up (intervalSlide t.down 1))) = m (c (f a))
    rw [intervalSlide_right]
    exact congrArg m (ConcreteCategory.congr_hom sqM.w a)
  let V := sqMI.desc U (fst C TopCat.I ≫ c ≫ m) hwU
  have hlV : (l ▷ TopCat.I) ≫ V = U := sqMI.inl_desc _ _ _
  have hcV : (c ▷ TopCat.I) ≫ V = fst C TopCat.I ≫ c ≫ m := sqMI.inr_desc _ _ _
  have hV₀ : TopCat.ι₀ ≫ V = m := by
    apply sqM.hom_ext
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hlV]
      ext ⟨a, t⟩
      change m (l (a, ULift.up (intervalSlide 0 t.down))) = m (l (a, t))
      simp only [intervalSlide_zero]
      rfl
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hcV,
        ← Category.assoc, TopCat.ι₀_fst, Category.id_comp]
  have hV₁ : TopCat.ι₁ ≫ V = m ≫ q ≫ s := by
    apply sqM.hom_ext
    · rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc, hlV,
        ← Category.assoc m q s, hmq, Category.assoc,
        ← Category.assoc l p, mappingCylinderProjection_cylinder, Category.assoc, hjs]
      ext ⟨a, t⟩
      change m (l (a, ULift.up (intervalSlide 1 t.down))) = m (c (f a))
      rw [intervalSlide_one]
      exact congrArg m (ConcreteCategory.congr_hom sqM.w a)
    · rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc, hcV,
        ← Category.assoc, TopCat.ι₁_fst, Category.id_comp, ← Category.assoc m q s, hmq,
          Category.assoc,
        ← Category.assoc c p, mappingCylinderProjection_target, Category.id_comp, hjs]
  have hUV : (i ▷ TopCat.I) ≫ K = ((TopCat.ι₀ ≫ l) ▷ TopCat.I) ≫ V := by
    rw [hK, comp_whiskerRight, Category.assoc, hlV]
    ext ⟨a, t⟩
    change m (l (a, t)) = m (l (a, ULift.up (intervalSlide t.down 0)))
    simp only [intervalSlide_left]
    rfl
  let sqQI := sqQ.map (tensorRight TopCat.I)
  let W := sqQI.desc K V hUV
  have hbW : (b ▷ TopCat.I) ≫ W = K := sqQI.inl_desc _ _ _
  have hmW : (m ▷ TopCat.I) ≫ W = V := sqQI.inr_desc _ _ _
  have hW₀ : TopCat.ι₀ ≫ W = 𝟙 Q := by
    apply sqQ.hom_ext
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hbW, hK₀, Category.comp_id]
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hmW, hV₀, Category.comp_id]
  have hW₁ : TopCat.ι₁ ≫ W = q ≫ s := by
    apply sqQ.hom_ext
    · rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc, hbW,
        ← Category.assoc b q s, hbq, hgs]
    · rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc, hmW, hV₁]
  exact ⟨q.hom, s.hom, ⟨(homotopyOfCylinder W hW₀ hW₁).symm⟩, ⟨right.symm⟩⟩

@[simp]
theorem mappingCylinderPushoutCollapseHomotopyEquiv_toFun
    {A B C M Q D : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    {b : B ⟶ Q} {m : M ⟶ Q} {g : B ⟶ D} {j : C ⟶ D}
    (sqM : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c)
    (sqQ : IsPushout i (TopCat.ι₀ ≫ l) b m)
    (sqD : IsPushout i f g j) (hi : homotopyExtensionProperty i) :
    (mappingCylinderPushoutCollapseHomotopyEquiv sqM sqQ sqD hi).toFun =
      (sqQ.desc g (mappingCylinderProjection sqM ≫ j)
        (by rw [Category.assoc, mappingCylinderProjection_start_assoc, sqD.w])).hom := rfl

/-- Replacing the forward map of a homotopy equivalence by a homotopic
specified map preserves an actual homotopy equivalence. -/
def homotopyEquivOfHomotopy {A B : TopCat.{u}}
    (e : ContinuousMap.HomotopyEquiv A B) {f : A ⟶ B}
    (H : f.hom.Homotopy e.toFun) : ContinuousMap.HomotopyEquiv A B where
  toFun := f.hom
  invFun := e.invFun
  left_inv := ⟨((ContinuousMap.Homotopy.refl e.invFun).comp H).trans e.left_inv.some⟩
  right_inv := ⟨(H.compContinuousMap e.invFun).trans e.right_inv.some⟩

/-- If the original map is a homotopy equivalence, so is the initial
endpoint inclusion into its mapping cylinder. Its forward map is exactly
the specified initial endpoint inclusion. -/
def mappingCylinderStartHomotopyEquiv {A C M : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c)
    (e : ContinuousMap.HomotopyEquiv A C) (he : e.toFun = f.hom) :
    ContinuousMap.HomotopyEquiv A M := by
  let ec := (mappingCylinderTargetStrongDeformationRetract sq).toHomotopyEquiv
  let H : TopCat.Homotopy (TopCat.ι₀ ≫ l) (f ≫ c) :=
    homotopyOfCylinder l rfl sq.w
  apply homotopyEquivOfHomotopy (e.trans ec)
  exact H.cast rfl (by change c.hom.comp f.hom = c.hom.comp e.toFun; rw [he])

@[simp]
theorem mappingCylinderStartHomotopyEquiv_toFun {A C M : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c)
    (e : ContinuousMap.HomotopyEquiv A C) (he : e.toFun = f.hom) :
    (mappingCylinderStartHomotopyEquiv sq e he).toFun = (TopCat.ι₀ ≫ l).hom := rfl

end Quillen.TheoremA
