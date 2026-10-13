/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.GrothendieckGroup.Basic
public import Quillen.Waldhausen.Cofinality.GradingRange

/-! # Actual representatives and original exact-functor naturality

Given genuine source factorization, every universal algebraic class has an
actual original object representative. Exact functors induce the expected
map on original classes. The quotient by its actual image is an explicit
additive grading, with precisely the algebraic image as its zero locus.
This does not identify that locus with a witnessed weak-image category.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v' u'' v'' w
namespace Quillen.Waldhausen.AlgebraicGrothendieck
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Every universal algebraic class is represented by an actual original object. -/
theorem objectClass_surjective (T : FunctorialFactorization W) : Function.Surjective
    (objectClass W) := by
  intro x
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (relations W) x
  change QuotientAddGroup.mk' (relations W) a ∈ (grading W).valueRange T
  induction a using FreeAbelianGroup.induction_on with
  | zero => simpa only [map_zero] using ((grading W).valueRange T).zero_mem
  | of A => exact ⟨A, rfl⟩
  | neg A h => simpa only [map_neg] using ((grading W).valueRange T).neg_mem h
  | add a b ha hb => simpa only [map_add] using ((grading W).valueRange T).add_mem ha hb

variable {D : Type u'} [Category.{v'} D] {V : Structure D}
  (F : C ⥤ D) (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- Pull back an actual additive grading along the original exact functor. -/
def pullbackGrading {G : Type w} [AddCommGroup G] (d : Cofinality.Grading V G) :
    Cofinality.Grading W G where
  value A := d.value (F.obj A)
  zero := (d.weak ((hF.zero W.isZero).iso V.isZero).hom (V.weq_iso _ inferInstance)).trans d.zero
  weak f hf := d.weak (F.map f) (hF.weak f hf)
  pushout hi hQ := d.pushout (hF.cofibration _ hi) (hF.pushout hi hQ)

/-- The original exact functor induces its canonical algebraic homomorphism. -/
def map : Group W →+ Group V := lift W (pullbackGrading W F hF (grading V))

/-- The image of an original class is the class of the original image object. -/
@[simp] theorem map_objectClass (A : C) : map W F hF (objectClass W A) = objectClass V (F.obj A) :=
  lift_objectClass W _ A

/-- The identity exact functor gives the literal identity algebraic homomorphism. -/
theorem map_id :
    map W (𝟭 C) (IsExact.id W.cof W.weq) = AddMonoidHom.id (Group W) := by
  apply hom_ext W
  intro A
  simp

variable {E : Type u''} [Category.{v''} E] {U : Structure E}
  (H : D ⥤ E) (hH : IsExact V.cof V.weq U.cof U.weq H)

/-- Original functor composition is retained by the canonical algebraic maps. -/
theorem map_comp :
    map W (F ⋙ H) (hF.comp hH) = (map V H hH).comp (map W F hF) := by
  apply hom_ext W
  intro A
  simp

end Quillen.Waldhausen.AlgebraicGrothendieck
