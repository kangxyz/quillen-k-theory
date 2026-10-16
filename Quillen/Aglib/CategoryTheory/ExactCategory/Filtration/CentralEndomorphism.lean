/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Hypothesis
public import Aglib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Dévissage for a locally nilpotent central endomorphism

A natural endomorphism of the identity gives a genuine dévissage property:
objects on which it vanishes. Its powers give actual finite image filtrations.
This construction will be applied to multiplication by an element on the
category of finite modules supported on its principal closed subset.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PrincipalSupportDevissage

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Objects annihilated by a natural central endomorphism. -/
def killed (t : 𝟭 C ⟶ 𝟭 C) : ObjectProperty C := fun X ↦ t.app X = 0

variable (t : 𝟭 C ⟶ 𝟭 C)

instance killed_containsZero : (killed t).ContainsZero :=
  ⟨⟨0, isZero_zero C, (isZero_zero C).eq_of_src _ _⟩⟩

instance killed_subobjects : (killed t).IsClosedUnderSubobjects where
  prop_of_mono {X Y} i _ h := by
    change t.app Y = 0 at h
    change t.app X = 0
    apply (cancel_mono i).1
    simpa only [Functor.id_map, h, comp_zero, zero_comp] using (t.naturality i).symm

instance killed_quotients : (killed t).IsClosedUnderQuotients where
  prop_of_epi {X Y} p _ h := by
    change t.app X = 0 at h
    change t.app Y = 0
    apply (cancel_epi p).1
    simpa only [Functor.id_map, h, comp_zero, zero_comp] using t.naturality p

instance killed_finiteProducts : (killed t).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := {
    limitsOfShape_le := by
      rintro X ⟨p⟩
      change t.app X = 0
      apply p.isLimit.hom_ext
      intro j
      have h : t.app (p.diag.obj j) = 0 := p.prop_diag_obj j
      have hn := t.naturality (p.cone.π.app j)
      change p.cone.π.app j ≫ t.app (p.diag.obj j) =
        t.app X ≫ p.cone.π.app j at hn
      rw [h, comp_zero] at hn
      simpa only [zero_comp] using hn.symm }

/-- The iterated central endomorphism, viewed as an actual categorical arrow. -/
def power (X : C) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => t.app X ≫ power X n

omit [Abelian C] in
@[simp] lemma power_zero (X : C) : power t X 0 = 𝟙 X := rfl

omit [Abelian C] in
@[simp] lemma power_succ (X : C) (n : ℕ) :
    power t X (n + 1) = t.app X ≫ power t X n := rfl

omit [Abelian C] in
lemma power_naturality {X Y : C} (a : X ⟶ Y) (n : ℕ) :
    power t X n ≫ a = a ≫ power t Y n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [power_succ, Category.assoc]
    rw [ih, ← Category.assoc]
    have hn : t.app X ≫ a = a ≫ t.app Y := (t.naturality a).symm
    rw [hn, Category.assoc]

/-- Multiplication by `t` lowers its nilpotence exponent on its actual image. -/
lemma image_power_eq_zero (X : C) (n : ℕ) (h : power t X (n + 1) = 0) :
    power t (image (t.app X)) n = 0 := by
  apply (cancel_mono (image.ι (t.app X))).1
  apply (cancel_epi (factorThruImage (t.app X))).1
  simp only [zero_comp, comp_zero]
  rw [power_naturality, ← Category.assoc, image.fac]
  exact h

/-- The quotient by the actual image of `t` is killed by `t`. -/
lemma killed_cokernel_image (X : C) :
    killed t (cokernel (image.ι (t.app X))) := by
  change t.app _ = 0
  apply (cancel_epi (cokernel.π (image.ι (t.app X)))).1
  rw [comp_zero]
  have hn := t.naturality (cokernel.π (image.ι (t.app X)))
  change cokernel.π (image.ι (t.app X)) ≫ t.app _ =
    t.app X ≫ cokernel.π (image.ι (t.app X)) at hn
  apply hn.trans
  calc
    _ = (factorThruImage (t.app X) ≫ image.ι (t.app X)) ≫
        cokernel.π (image.ι (t.app X)) :=
      congrArg (fun a ↦ a ≫ cokernel.π (image.ι (t.app X))) (image.fac (t.app X)).symm
    _ = 0 := by rw [Category.assoc, cokernel.condition, comp_zero]

/-- The finite image filtration is assembled from actual image inclusions and
cokernels. Each step decreases the annihilating exponent by one. -/
theorem filtration_of_power_eq_zero (n : ℕ) (X : C) (h : power t X n = 0) :
    Nonempty ((abelianExactStructure C).Filtration (killed t) X) := by
  induction n generalizing X with
  | zero =>
    refine ⟨.zero ?_⟩
    exact (IsZero.iff_id_eq_zero X).2 (by simpa using h)
  | succ n ih =>
    let i := image.ι (t.app X)
    obtain ⟨F⟩ := ih (image (t.app X)) (image_power_eq_zero t X n h)
    exact ⟨.step (ShortComplex.mk i (cokernel.π i) (cokernel.condition i))
      { exact := ShortComplex.cokernelSequence_exact i } F (killed_cokernel_image t X)⟩

/-- Objectwise nilpotence supplies the complete classical dévissage hypothesis. -/
theorem filtrationHypothesis (h : ∀ X : C, ∃ n : ℕ, power t X n = 0) :
    Devissage.FiltrationHypothesis (killed t) := by
  intro X
  obtain ⟨n, hn⟩ := h X
  exact filtration_of_power_eq_zero t n X hn

section Scalar
variable {R : Type u} [CommRing R]
variable (F : C ⥤ FGModuleCat.{u} R) [F.Full] [F.Faithful]

/-- Scalar multiplication pulled back through a fully faithful representation. -/
def scalar (f : R) : 𝟭 C ⟶ 𝟭 C where
  app X := F.preimage (FGModuleCat.ofHom (LinearMap.lsmul R (F.obj X) f))
  naturality {X Y} a := by
    apply F.map_injective
    simp only [Functor.id_map, Functor.map_comp, Functor.map_preimage]
    ext m
    exact ((F.map a).hom.hom.map_smul f m).symm

omit [Abelian C] in
@[simp] lemma map_scalar (f : R) (X : C) :
    F.map ((scalar F f).app X) =
      FGModuleCat.ofHom (LinearMap.lsmul R (F.obj X) f) := F.map_preimage _

omit [Abelian C] in
lemma map_power_apply (f : R) (X : C) (n : ℕ) (m : F.obj X) :
    (F.map (power (scalar F f) X n)).hom.hom m = f ^ n • m := by
  induction n with
  | zero => simp [power]
  | succ n ih =>
    simp only [power_succ, Functor.map_comp, map_scalar]
    change (F.map (power (scalar F f) X n)).hom.hom (f • m) = f ^ (n + 1) • m
    rw [map_smul, ih, smul_smul, pow_succ']

variable [F.Additive]

lemma scalar_killed_iff (f : R) (X : C) :
    killed (scalar F f) X ↔ ∀ m : F.obj X, f • m = 0 := by
  change (scalar F f).app X = 0 ↔ _
  rw [← F.map_injective.eq_iff, map_scalar, F.map_zero]
  constructor
  · intro h m
    exact congrArg (fun a ↦ a.hom.hom m) h
  · intro h
    ext m
    exact h m

lemma scalar_power_eq_zero (f : R) (X : C) (n : ℕ)
    (h : ∀ m : F.obj X, f ^ n • m = 0) : power (scalar F f) X n = 0 := by
  apply F.map_injective
  rw [F.map_zero]
  ext m
  exact (map_power_apply F f X n m).trans (h m)

end Scalar

end Quillen.PrincipalSupportDevissage

