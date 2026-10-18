/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.RepresentationTheory.Homological.GroupHomology.PerfectBarExtension

/-!
# Central-extension evaluation and lifts from integral bar homology

Intended upstream module: `Aglib.RepresentationTheory.Homological.GroupHomology.CentralBarLifts`.
The original Mathlib bar complex uses a commutative coefficient ring and a group.
Chosen cocycles and extension perfectness retain their perfect-group hypotheses;
integral comparisons use `ULift ℤ`, and central lifts retain surjectivity and central kernel.
Current consumer: `Quillen.Algebra.Group.StableSteinbergSchur`.
-/
@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits Finsupp
open scoped IsMulCommutative
namespace groupHomology.IntegralBar
section Descent
variable {k G M : Type u} [CommRing k] [Group G] [AddCommGroup M] [Module k M]
  (l : (G × G →₀ k) →ₗ[k] M)
  (hl : l.comp (groupHomology.d₃₂ (coefficients k G)).hom = 0)

/-- Evaluation killing the ORIGINAL bar three-boundaries descends to native H-two. -/
def homologyDesc : groupHomology.H2 (coefficients k G) →ₗ[k] M := by
  let S := groupHomology.shortComplexH2 (coefficients k G)
  let h := S.moduleCatLeftHomologyData
  let v : h.K ⟶ ModuleCat.of k M := ModuleCat.ofHom
    (l.comp (groupHomology.cycles₂ (coefficients k G)).subtype)
  have hv : h.f' ≫ v = 0 := by
    apply ModuleCat.hom_ext
    ext c
    exact LinearMap.congr_fun hl c
  exact ((groupHomology.H2Iso (coefficients k G)).hom ≫ h.descH v hv).hom

/-- The descent evaluates every original two-cycle without changing its representative. -/
theorem homologyDesc_pi (c : groupHomology.cycles₂ (coefficients k G)) :
    homologyDesc l hl (groupHomology.H2π (coefficients k G) c) = l c.val := by
  let S := groupHomology.shortComplexH2 (coefficients k G)
  let h := S.moduleCatLeftHomologyData
  have he : groupHomology.H2π (coefficients k G) ≫
      (groupHomology.H2Iso (coefficients k G)).hom = h.π := by
    rw [← groupHomology.π_comp_H2Iso_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (groupHomology.H2π (coefficients k G) ≫
    ((groupHomology.H2Iso (coefficients k G)).hom ≫ h.descH _ _)) c = _
  rw [← Category.assoc, he, h.π_descH]
  rfl
end Descent

variable {G H : Type u} [Group G] [Group H]
  (p : H →* G) (hp : Function.Surjective p) (hc : p.ker ≤ Subgroup.center H)

/-- A genuine section of the supplied surjection, normalized at the original identity. -/
def centralSection (g : G) : H := by
  classical
  exact if g = 1 then 1 else (hp g).choose

@[simp] theorem centralSection_one : centralSection p hp 1 = 1 := by simp [centralSection]

/-- The actual chosen lifts project to their original group elements. -/
@[simp] theorem centralSection_projection (g : G) : p (centralSection p hp g) = g := by
  classical
  by_cases hg : g = 1
  · subst g; simp
  · simp only [centralSection, ite_eq_right hg]
    exact (hp g).choose_spec

/-- The multiplicative section defect is an actual central element by the given central kernel. -/
def sectionDefect (g h : G) : Subgroup.center H :=
  ⟨centralSection p hp g * centralSection p hp h * (centralSection p hp (g * h))⁻¹,
    hc (by simp only [MonoidHom.mem_ker, map_mul, map_inv, centralSection_projection,
      mul_inv_cancel])⟩

/-- Multiplication of the chosen section has the displayed original central defect. -/
theorem sectionDefect_section (g h : G) :
    centralSection p hp g * centralSection p hp h =
      (sectionDefect p hp hc g h).val * centralSection p hp (g * h) := by
  simp [sectionDefect, mul_assoc]

/-- Associativity proves the actual central-defect cocycle identity. -/
theorem sectionDefect_cocycle (g h j : G) :
    sectionDefect p hp hc g h * sectionDefect p hp hc (g * h) j =
      sectionDefect p hp hc h j * sectionDefect p hp hc g (h * j) := by
  apply Subtype.ext
  change (sectionDefect p hp hc g h).val * (sectionDefect p hp hc (g * h) j).val = _
  calc
    _ = (centralSection p hp g * centralSection p hp h * centralSection p hp j) *
        (centralSection p hp (g * (h * j)))⁻¹ := by
      simp only [sectionDefect, mul_assoc]
      group
    _ = centralSection p hp g * (sectionDefect p hp hc h j).val *
        centralSection p hp (h * j) * (centralSection p hp (g * (h * j)))⁻¹ := by
      simp only [sectionDefect]
      group
    _ = (sectionDefect p hp hc h j).val * centralSection p hp g *
        centralSection p hp (h * j) * (centralSection p hp (g * (h * j)))⁻¹ := by
      rw [Subgroup.mem_center_iff.mp (sectionDefect p hp hc h j).property]
    _ = _ := by simp only [Subgroup.coe_mul, sectionDefect, mul_assoc]

/-- Extend the actual section defect linearly on the existing lifted-integral bar chains. -/
def defectEvaluation : (G × G →₀ ULift.{u} ℤ) →ₗ[ULift.{u} ℤ] Additive (Subgroup.center H) :=
  Finsupp.lsum (ULift.{u} ℤ) (fun gh => LinearMap.toSpanSingleton (ULift.{u} ℤ) _
    (Additive.ofMul (sectionDefect p hp hc gh.1 gh.2)))

/-- Evaluation of each original unit bar is the actual section defect. -/
@[simp] theorem defectEvaluation_single_one (g h : G) :
    defectEvaluation p hp hc (single (g, h) 1) =
      Additive.ofMul (sectionDefect p hp hc g h) := by
  simp [defectEvaluation]

/-- The original three-bar differential is annihilated by the proved central-defect cocycle. -/
theorem defectEvaluation_boundary :
    (defectEvaluation p hp hc).comp
      (groupHomology.d₃₂ (coefficients (ULift.{u} ℤ) G)).hom = 0 := by
  apply Finsupp.lhom_ext
  intro ghk a
  have hs : single ghk a = a • single ghk (1 : ULift.{u} ℤ) := by simp
  rw [hs, map_smul]
  change a • defectEvaluation p hp hc
    (groupHomology.d₃₂ (coefficients (ULift.{u} ℤ) G) (single ghk 1)) = 0
  suffices hz : defectEvaluation p hp hc
      (groupHomology.d₃₂ (coefficients (ULift.{u} ℤ) G) (single ghk 1)) = 0 by rw [hz, smul_zero]
  rcases ghk with ⟨g, h, j⟩
  rw [dThree_single, map_sub, map_add, map_sub, defectEvaluation_single_one,
    defectEvaluation_single_one, defectEvaluation_single_one, defectEvaluation_single_one]
  have hcycle := congrArg Additive.ofMul (sectionDefect_cocycle p hp hc g h j)
  change Additive.ofMul (sectionDefect p hp hc g h) +
      Additive.ofMul (sectionDefect p hp hc (g * h) j) =
    Additive.ofMul (sectionDefect p hp hc h j) +
      Additive.ofMul (sectionDefect p hp hc g (h * j)) at hcycle
  calc
    _ = (Additive.ofMul (sectionDefect p hp hc h j) +
        Additive.ofMul (sectionDefect p hp hc g (h * j))) -
      (Additive.ofMul (sectionDefect p hp hc g h) +
        Additive.ofMul (sectionDefect p hp hc (g * h) j)) := by abel
    _ = 0 := sub_eq_zero.mpr hcycle.symm

/-- The actual section defect induces an actual homomorphism on the native second homology. -/
def centralHomologyEvaluation : groupHomology.H2 (coefficients (ULift.{u} ℤ) G) →ₗ[ULift.{u} ℤ]
    Additive (Subgroup.center H) :=
  homologyDesc (defectEvaluation p hp hc) (defectEvaluation_boundary p hp hc)

end groupHomology.IntegralBar

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Finsupp
open scoped IsMulCommutative
namespace groupHomology.IntegralBar
variable {G H : Type u} [Group G] [Group H]
  (p : H →* G) (hp : Function.Surjective p) (hc : p.ker ≤ Subgroup.center H)

/-- The actual defect projects to identity in the original quotient group. -/
theorem sectionDefect_projection (g h : G) : p (sectionDefect p hp hc g h).val = 1 := by
  simp only [sectionDefect, map_mul, map_inv, centralSection_projection, mul_inv_cancel]

/-- Every evaluated original bar chain lies in the actual projection kernel. -/
theorem defectEvaluation_projection (c : G × G →₀ ULift.{u} ℤ) :
    p (defectEvaluation p hp hc c).toMul.val = 1 := by
  induction c using Finsupp.induction with
  | zero => rw [map_zero]; exact map_one p
  | @single_add gh a c _ _ ih =>
    rw [map_add]
    change p ((defectEvaluation p hp hc (single gh a)).toMul.val *
      (defectEvaluation p hp hc c).toMul.val) = 1
    rw [map_mul, ih, mul_one]
    simp only [defectEvaluation, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]
    change p (((a • Additive.ofMul (sectionDefect p hp hc gh.1 gh.2)).toMul).val) = 1
    change p ((sectionDefect p hp hc gh.1 gh.2).val ^ a.down) = 1
    rw [map_zpow, sectionDefect_projection, one_zpow]

/-- Native H-two descent retains membership in the original central kernel. -/
theorem centralHomologyEvaluation_projection (a : groupHomology.H2
    (coefficients (ULift.{u} ℤ) G)) : p (centralHomologyEvaluation p hp hc a).toMul.val = 1 := by
  induction a using groupHomology.H2_induction_on with
  | h c =>
    change p (homologyDesc (defectEvaluation p hp hc) (defectEvaluation_boundary p hp hc)
      (groupHomology.H2π (coefficients (ULift.{u} ℤ) G) c)).toMul.val = 1
    rw [homologyDesc_pi]
    exact defectEvaluation_projection p hp hc c.val

variable [Group.IsPerfect G]

/-- Evaluating the original bar cocycle gives the exact defect of the original chosen fillers. -/
theorem centralHomologyEvaluation_barCocycle (g h : G) :
    centralHomologyEvaluation p hp hc (barCocycle (ULift.{u} ℤ) G g h) =
      defectEvaluation p hp hc (filler (ULift.{u} ℤ) G g) +
      defectEvaluation p hp hc (filler (ULift.{u} ℤ) G h) -
      defectEvaluation p hp hc (filler (ULift.{u} ℤ) G (g * h)) -
      Additive.ofMul (sectionDefect p hp hc g h) := by
  change homologyDesc (defectEvaluation p hp hc) (defectEvaluation_boundary p hp hc)
    (groupHomology.H2π (coefficients (ULift.{u} ℤ) G) (fillerCycle (ULift.{u} ℤ) G g h)) = _
  rw [homologyDesc_pi]
  change defectEvaluation p hp hc (_ + _ - _ - _) = _
  rw [map_sub, map_sub, map_add, defectEvaluation_single_one]

/-- The actual central correction combines the original H-two class and its chosen bar filler. -/
def liftCorrection (a : IntegralBarExtension G) : Subgroup.center H :=
  (centralHomologyEvaluation p hp hc a.homology +
    defectEvaluation p hp hc (filler (ULift.{u} ℤ) G a.base)).toMul

/-- The correction remains in the kernel of the original projection. -/
theorem liftCorrection_projection (a : IntegralBarExtension G) :
    p (liftCorrection p hp hc a).val = 1 := by
  change p ((centralHomologyEvaluation p hp hc a.homology).toMul.val *
    (defectEvaluation p hp hc (filler (ULift.{u} ℤ) G a.base)).toMul.val) = 1
  rw [map_mul, centralHomologyEvaluation_projection, defectEvaluation_projection, one_mul]

/-- The correction has the exact multiplicative coboundary required by the original section. -/
theorem liftCorrection_mul (a b : IntegralBarExtension G) :
    liftCorrection p hp hc (a * b) = liftCorrection p hp hc a * liftCorrection p hp hc b *
      (sectionDefect p hp hc a.base b.base)⁻¹ := by
  change (centralHomologyEvaluation p hp hc
      (a.homology + b.homology + barCocycle (ULift.{u} ℤ) G a.base b.base) +
    defectEvaluation p hp hc (filler (ULift.{u} ℤ) G (a.base * b.base))).toMul = _
  have h : centralHomologyEvaluation p hp hc
      (a.homology + b.homology + barCocycle (ULift.{u} ℤ) G a.base b.base) +
      defectEvaluation p hp hc (filler (ULift.{u} ℤ) G (a.base * b.base)) =
    (centralHomologyEvaluation p hp hc a.homology +
      defectEvaluation p hp hc (filler (ULift.{u} ℤ) G a.base)) +
    (centralHomologyEvaluation p hp hc b.homology +
      defectEvaluation p hp hc (filler (ULift.{u} ℤ) G b.base)) -
      Additive.ofMul (sectionDefect p hp hc a.base b.base) := by
    rw [map_add, map_add, centralHomologyEvaluation_barCocycle]
    abel
  apply Subtype.ext
  have h' := congrArg (fun z : Additive (Subgroup.center H) => z.toMul.val) h
  have hcancel : Additive.toMul (Additive.ofMul (sectionDefect p hp hc a.base b.base)) =
      sectionDefect p hp hc a.base b.base := Additive.ofMul.symm_apply_apply _
  simpa only [liftCorrection, toMul_add, toMul_sub,
    Subgroup.coe_mul, Subgroup.coe_div, div_eq_mul_inv, hcancel] using h'

/-- The correction is genuinely normalized at the group identity. -/
theorem liftCorrection_one : liftCorrection p hp hc (1 : IntegralBarExtension G) = 1 := by
  change (centralHomologyEvaluation p hp hc 0 +
    defectEvaluation p hp hc (filler (ULift.{u} ℤ) G 1)).toMul = 1
  rw [map_zero, zero_add, filler_one, defectEvaluation_single_one]
  apply Subtype.ext
  simp [sectionDefect]

/-- The concrete bar extension lifts to the supplied actual central extension. -/
def barLift : IntegralBarExtension G →* H where
  toFun a := (liftCorrection p hp hc a).val⁻¹ * centralSection p hp a.base
  map_one' := by
    rw [liftCorrection_one]
    change (1 : H)⁻¹ * centralSection p hp 1 = 1
    simp
  map_mul' a b := by
    rw [liftCorrection_mul]
    change ((liftCorrection p hp hc a).val * (liftCorrection p hp hc b).val *
      (sectionDefect p hp hc a.base b.base).val⁻¹)⁻¹ * centralSection p hp (a.base * b.base) =
        ((liftCorrection p hp hc a).val⁻¹ * centralSection p hp a.base) *
          ((liftCorrection p hp hc b).val⁻¹ * centralSection p hp b.base)
    have hz₀ : Commute (centralSection p hp a.base) (liftCorrection p hp hc b).val :=
      Subgroup.mem_center_iff.mp (liftCorrection p hp hc b).property _
    have hz := hz₀.inv_right
    have hd : Commute (sectionDefect p hp hc a.base b.base).val
        ((liftCorrection p hp hc a).val⁻¹ * (liftCorrection p hp hc b).val⁻¹) :=
      (Subgroup.mem_center_iff.mp (sectionDefect p hp hc a.base b.base).property _).symm
    have hab₀ : Commute (liftCorrection p hp hc a).val (liftCorrection p hp hc b).val :=
      (Subgroup.mem_center_iff.mp (liftCorrection p hp hc a).property _).symm
    have hab := hab₀.inv_left.inv_right
    rw [mul_inv_rev, inv_inv, mul_inv_rev, hab.symm.eq, hd.eq, mul_assoc,
      ← sectionDefect_section]
    rw [← mul_assoc, mul_assoc (liftCorrection p hp hc a).val⁻¹,
      hz.symm.eq]
    simp only [mul_assoc]

/-- The constructed lift lies over the original group projection. -/
theorem barLift_over : p.comp (barLift p hp hc) = barProjection (ULift.{u} ℤ) G := by
  ext a
  change p ((liftCorrection p hp hc a).val⁻¹ * centralSection p hp a.base) = a.base
  rw [map_mul, map_inv, liftCorrection_projection, inv_one, one_mul, centralSection_projection]

end groupHomology.IntegralBar

end
