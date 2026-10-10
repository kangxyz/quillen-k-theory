/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.GrothendieckGroup.Image

/-! # Original algebraic classes, exact functors and actual image-quotient consumers -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v' w
namespace Quillen.Tests.WaldhausenGrothendieckGroup
open Waldhausen AlgebraicGrothendieck
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- An actual original weak comparison identifies the two displayed original object classes. -/
theorem original_weak_class {A B : C} (f : A ⟶ B) (hf : W.weq f) :
    objectClass W A = objectClass W B := objectClass_weak W f hf

/-- The original displayed cofiber, rather than an isomorphic replacement, has the difference class.
  -/
theorem original_cofiber_class {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : W.cof i) (hQ : IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q)) :
    objectClass W Q = objectClass W B - objectClass W A :=
  (grading W).cofiber_value hi hQ

/-- Every algebraic class has one actual object representative from genuine source factorization. -/
theorem actual_class_representative (T : FunctorialFactorization W) (x : Group W) :
    ∃ A : C, objectClass W A = x := objectClass_surjective W T x

/-- Any outgoing homomorphism with the specified original object values is the canonical lift. -/
theorem original_values_determine_lift {G : Type w} [AddCommGroup G]
    (d : Cofinality.Grading W G) (f : Group W →+ G)
    (hf : ∀ A : C, f (objectClass W A) = d.value A) : f = lift W d :=
  (universal W d).unique hf (lift_objectClass W d)

variable {D : Type u'} [Category.{v'} D] {V : Structure D}
  (F : C ⥤ D) (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- Actual original image objects exhaust the algebraic image under genuine source factorization. -/
theorem original_image_class_representative (T : FunctorialFactorization W)
    (g : Group V) (hg : g ∈ (map W F hF).range) :
    ∃ A : C, objectClass V (F.obj A) = g := (mem_range_iff_image_object W F hF T g).mp hg

/-- An actual witnessed weak-image target lies in the zero-grade full subcategory. -/
theorem witnessed_image_is_zero_grade {A : D} (hA : ApproximationImage.objects V F A) :
    Fibration.acyclicObjects (imageQuotientGrading W F hF).nested A :=
  ((imageQuotientGrading W F hF).acyclicObjects_iff A).mpr
    (imageQuotientGrading_zero_of_weakImage W F hF hA)

/-- The converse available at this stage is exactly algebraic image membership. -/
theorem zero_grade_is_original_algebraic_image (A : D) :
    Fibration.acyclicObjects (imageQuotientGrading W F hF).nested A ↔
      objectClass V A ∈ (map W F hF).range :=
  ((imageQuotientGrading W F hF).acyclicObjects_iff A).trans (imageQuotientGrading_zero_iff W F hF
    A)

/-- The exact image quotient has an original target representative for each of its actual elements.
  -/
theorem quotient_class_representative (T : FunctorialFactorization V) (x : ImageQuotient W F hF) :
    ∃ A : D, (imageQuotientGrading W F hF).value A = x := imageQuotientGrading_surjective W F hF T x
end Quillen.Tests.WaldhausenGrothendieckGroup
