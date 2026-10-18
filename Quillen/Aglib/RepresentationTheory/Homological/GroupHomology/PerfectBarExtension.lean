/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.RepresentationTheory.Homological.GroupHomology.IntegralBar
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Ring.ULift

/-!
# Perfectness of the integral bar extension

Intended upstream module:
  `Aglib.RepresentationTheory.Homological.GroupHomology.PerfectBarExtension`.
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
open CategoryTheory Finsupp
namespace groupHomology.IntegralBar
variable (k G : Type u) [CommRing k] [Group G] [Group.IsPerfect G]

/-- Extend the actual one-generator fillers linearly on the existing bar one-chains. -/
def fillerLinear : (G →₀ k) →ₗ[k] (G × G →₀ k) :=
  Finsupp.lsum k (fun g => LinearMap.toSpanSingleton k _ (filler k G g))

/-- The original chosen unit-generator filler is retained. -/
@[simp] theorem fillerLinear_single (g : G) (c : k) :
    fillerLinear k G (single g c) = c • filler k G g :=
  Finsupp.lsum_single _ _ _ _

/-- Linearity of the actual bar differential makes the displayed fillers a section. -/
theorem fillerLinear_boundary (c : G →₀ k) :
    groupHomology.d₂₁ (coefficients k G) (fillerLinear k G c) = c := by
  have h : (groupHomology.d₂₁ (coefficients k G)).hom.comp (fillerLinear k G) =
      LinearMap.id := by
    apply Finsupp.lhom_ext
    intro g a
    change groupHomology.d₂₁ (coefficients k G) (fillerLinear k G (single g a)) = single g a
    rw [fillerLinear_single, map_smul]
    erw [filler_boundary]
    simp
  exact LinearMap.congr_fun h c

/-- The lifted boundary minus the original two-chain, `W d₂ - id`; it is `-id` on cycles. -/
def cycleRetraction : (G × G →₀ k) →ₗ[k] groupHomology.cycles₂ (coefficients k G) :=
  ((fillerLinear k G).comp (groupHomology.d₂₁ (coefficients k G)).hom - LinearMap.id).codRestrict
    (groupHomology.cycles₂ (coefficients k G)) (by
      intro c
      change groupHomology.d₂₁ (coefficients k G)
        (fillerLinear k G (groupHomology.d₂₁ (coefficients k G) c) - c) = 0
      rw [map_sub, fillerLinear_boundary, sub_self])

/-- The original bar generator is sent precisely to the constructed filler cycle. -/
theorem cycleRetraction_single_one (g h : G) :
    cycleRetraction k G (single (g, h) 1) = fillerCycle k G g h := by
  apply Subtype.ext
  change fillerLinear k G (groupHomology.d₂₁ (coefficients k G) (single (g, h) 1)) -
    single (g, h) 1 = _
  rw [dTwo_single, map_add, map_sub, fillerLinear_single, fillerLinear_single, fillerLinear_single]
  simp only [one_smul, fillerCycle]
  abel

/-- On an actual two-cycle the retraction is its negative, as an exact cycle equality. -/
theorem cycleRetraction_cycle (c : groupHomology.cycles₂ (coefficients k G)) :
    cycleRetraction k G c.val = -c := by
  apply Subtype.ext
  change fillerLinear k G (groupHomology.d₂₁ (coefficients k G) c.val) - c.val = -c.val
  rw [show groupHomology.d₂₁ (coefficients k G) c.val = 0 from c.property, map_zero, zero_sub]

/-- The actual homology projection of that retraction is the linear extension of the cocycle. -/
def cycleValue : (G × G →₀ k) →ₗ[k] groupHomology.H2 (coefficients k G) :=
  (groupHomology.H2π (coefficients k G)).hom.comp (cycleRetraction k G)

/-- The unit bar generator retains the constructed original H-two cocycle. -/
@[simp] theorem cycleValue_single_one (g h : G) :
    cycleValue k G (single (g, h) 1) = barCocycle k G g h := by
  change groupHomology.H2π (coefficients k G) _ = _
  rw [cycleRetraction_single_one]
  rfl

/-- An actual cycle evaluates to the negative of its original H-two class. -/
theorem cycleValue_cycle (c : groupHomology.cycles₂ (coefficients k G)) :
    cycleValue k G c.val = -groupHomology.H2π (coefficients k G) c := by
  change groupHomology.H2π (coefficients k G) _ = _
  rw [cycleRetraction_cycle, map_neg]

end groupHomology.IntegralBar

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory Finsupp
namespace groupHomology.IntegralBar

/-- Additive maps respect the actual lifted integer scalar action. -/
def liftedIntLinearMap {A : Type v} {B : Type w} [AddCommGroup A] [AddCommGroup B]
    [Module (ULift.{u} ℤ) A] [Module (ULift.{u} ℤ) B] (f : A →+ B) :
    A →ₗ[ULift.{u} ℤ] B where
  toFun := f
  map_add' := f.map_add
  map_smul' c a := by
    simp only [RingHom.id_apply]
    have hc : c = (c.down : ULift.{u} ℤ) := by cases c; rfl
    rw [hc, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    exact map_zsmul f c.down a

variable (G : Type u) [Group G] [Group.IsPerfect G]

/-- The coefficient ring is the actual integer ring lifted to the group's universe. -/
abbrev IntegralBarExtension := BarExtension (ULift.{u} ℤ) G

/-- The canonical kernel inclusion followed by the ACTUAL abelianization map. -/
def abKernel : groupHomology.H2 (coefficients (ULift.{u} ℤ) G) →+
    Additive (Abelianization (IntegralBarExtension G)) where
  toFun a := Additive.ofMul (Abelianization.of (⟨a, 1⟩ : IntegralBarExtension G))
  map_zero' := map_one Abelianization.of
  map_add' a b := by
    change Abelianization.of (⟨a + b, 1⟩ : IntegralBarExtension G) =
      Abelianization.of (⟨a, 1⟩ : IntegralBarExtension G) *
        Abelianization.of (⟨b, 1⟩ : IntegralBarExtension G)
    rw [← map_mul]
    apply congrArg Abelianization.of
    apply BarExtension.ext
    · change a + b = a + b + barCocycle (ULift.{u} ℤ) G 1 1
      simp
    · exact (one_mul _).symm

/-- The zero-homology section, evaluated in the actual abelianization. -/
def abSection (g : G) : Additive (Abelianization (IntegralBarExtension G)) :=
  Additive.ofMul (Abelianization.of (⟨0, g⟩ : IntegralBarExtension G))

/-- The actual abelianization of each cocycle value is the section coboundary. -/
theorem abKernel_barCocycle (g h : G) :
    abKernel G (barCocycle (ULift.{u} ℤ) G g h) =
      abSection G g + abSection G h - abSection G (g * h) := by
  apply (eq_sub_iff_add_eq).mpr
  change Abelianization.of (⟨barCocycle (ULift.{u} ℤ) G g h, 1⟩ : IntegralBarExtension G) *
      Abelianization.of (⟨0, g * h⟩ : IntegralBarExtension G) =
    Abelianization.of (⟨0, g⟩ : IntegralBarExtension G) *
      Abelianization.of (⟨0, h⟩ : IntegralBarExtension G)
  rw [← map_mul, ← map_mul]
  apply congrArg Abelianization.of
  apply BarExtension.ext
  · change barCocycle (ULift.{u} ℤ) G g h + 0 + barCocycle (ULift.{u} ℤ) G 1 (g * h) =
      0 + 0 + barCocycle (ULift.{u} ℤ) G g h
    simp
  · exact one_mul _

/-- The actual section extends linearly on the original integral bar one-chains. -/
def abSectionLinear : (G →₀ ULift.{u} ℤ) →ₗ[ULift.{u} ℤ]
    Additive (Abelianization (IntegralBarExtension G)) :=
  Finsupp.lsum (ULift.{u} ℤ) (fun g =>
    LinearMap.toSpanSingleton (ULift.{u} ℤ) _ (abSection G g))

/-- The actual kernel map extends to the coefficient ring by its canonical integer action. -/
def abKernelLinear : groupHomology.H2 (coefficients (ULift.{u} ℤ) G) →ₗ[ULift.{u} ℤ]
    Additive (Abelianization (IntegralBarExtension G)) := liftedIntLinearMap (abKernel G)

/-- The complete original bar-chain equation realizes the abelianized kernel as a coboundary. -/
theorem abKernel_cycleValue :
    (abKernelLinear G).comp (cycleValue (ULift.{u} ℤ) G) =
      (abSectionLinear G).comp (groupHomology.d₂₁ (coefficients (ULift.{u} ℤ) G)).hom := by
  apply Finsupp.lhom_ext
  intro gh a
  have hsingle : single gh a = a • single gh (1 : ULift.{u} ℤ) := by simp
  rw [hsingle, map_smul, map_smul]
  congr 1
  rcases gh with ⟨g, h⟩
  change abKernelLinear G (cycleValue (ULift.{u} ℤ) G (single (g, h) 1)) =
    abSectionLinear G (groupHomology.d₂₁ (coefficients (ULift.{u} ℤ) G) (single (g, h) 1))
  rw [cycleValue_single_one, dTwo_single, map_add, map_sub]
  change abKernel G (barCocycle (ULift.{u} ℤ) G g h) = _
  rw [abKernel_barCocycle]
  simp only [abSectionLinear, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
    one_smul]
  abel

/-- Every original H-two kernel element vanishes in the actual abelianization. -/
theorem abKernel_zero (a : groupHomology.H2 (coefficients (ULift.{u} ℤ) G)) :
    abKernel G a = 0 := by
  induction a using groupHomology.H2_induction_on with
  | h c =>
    have h := LinearMap.congr_fun (abKernel_cycleValue G) c.val
    change abKernelLinear G (cycleValue (ULift.{u} ℤ) G c.val) =
      abSectionLinear G (groupHomology.d₂₁ (coefficients (ULift.{u} ℤ) G) c.val) at h
    rw [cycleValue_cycle, map_neg,
      show groupHomology.d₂₁ (coefficients (ULift.{u} ℤ) G) c.val = 0 from c.property,
      map_zero] at h
    exact neg_eq_zero.mp h

/-- The original integral bar projection kernel is contained in the actual commutator. -/
theorem integralBar_ker_le_commutator :
    (barProjection (ULift.{u} ℤ) G).ker ≤ commutator (IntegralBarExtension G) := by
  intro a ha
  rw [← Abelianization.ker_of]
  rcases a with ⟨a, g⟩
  change g = 1 at ha
  subst g
  exact congrArg Additive.toMul (abKernel_zero G a)

/-- The concrete integral bar extension is perfect; this is a theorem, not extension data. -/
theorem integralBar_isPerfect : Group.IsPerfect (IntegralBarExtension G) := by
  let p := barProjection (ULift.{u} ℤ) G
  have hs := barProjection_surjective (ULift.{u} ℤ) G
  have hk := integralBar_ker_le_commutator G
  have hc : (commutator (IntegralBarExtension G)).map p = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective p hs]
    exact Group.IsPerfect.commutator_eq_top
  refine ⟨top_unique ?_⟩
  intro a _
  have ha : p a ∈ (commutator (IntegralBarExtension G)).map p := by rw [hc]; trivial
  obtain ⟨c, hc, he⟩ := ha
  have hd : a * c⁻¹ ∈ commutator (IntegralBarExtension G) := hk (by
    change p (a * c⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel])
  simpa only [inv_mul_cancel_right] using (commutator (IntegralBarExtension G)).mul_mem hd hc

end groupHomology.IntegralBar

end
