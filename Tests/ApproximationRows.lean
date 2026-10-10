/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Approximation.Rows

/-! Behavioral consumers for actual row approximation and its original maps. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
open Quillen.Waldhausen Quillen.Waldhausen.QuotientRows
universe u v u' v'
namespace ApproximationRowsConsumers
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}

/-- Quotient descent preserves every specified initial component exactly. -/
theorem original_initial_component {n : SimplexCategory} {A B : Obj W n}
    (a : (initialFlagFunctor W n).obj A ⟶ (initialFlagFunctor W n).obj B)
    (i : Fin (n.len+1)) :
    (extendInitialFlagMap W a).hom.app (interval 0 i (Fin.zero_le _)) = a.app i :=
  extendInitialFlagAt_initial W a i

/-- Every original row map is recovered by descent of its own initial components. -/
theorem original_map_recovered {n : SimplexCategory} {A B : Obj W n} (f : A ⟶ B) :
    extendInitialFlagMap W ((initialFlagFunctor W n).map f) = f :=
  (initialFlagFullyFaithful W n).preimage_map f

/-- The comparison from a flag to its genuine completion is its original quotient map. -/
theorem completion_original_quotient {n : SimplexCategory}
    (L : WeakFlag W.cof W.weq n.len) (i : Fin (n.len+1)) :
    (completionFlagIso W L).hom.app i =
      completionQuotient W L.diagram L.cofibration (interval 0 i (Fin.zero_le _)) := rfl

/-- Weakness on the initial flag propagates to every actual quotient by gluing. -/
theorem every_quotient_weak {n : SimplexCategory} {A B : Obj W n} (f : A ⟶ B)
    (hf : ∀ i, W.weq (f.hom.app (interval 0 i (Fin.zero_le _)))) (p : Interval n) :
    W.weq (f.hom.app p) := (weq_iff_initialFlag W f).2 hf p

variable (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W))

/-- The unrestricted lift factors each original component exactly. -/
theorem actual_lift_component_factorization {n : SimplexCategory} {A : Obj W n} {B : Obj V n}
    (f : (postcompose W V hF n).obj A ⟶ B) (p : Interval n) :
    F.map ((h.rowLiftInclusion hF f).hom.app p) ≫ (h.rowLiftProjection hF f).hom.app p = f.hom.app p
      :=
  congrArg (fun a ↦ a.hom.app p) (h.rowLift_factorization hF f)

/-- The honest source factorization satisfies every horizontal joint cofibration test. -/
theorem factorization_joint_test {n : SimplexCategory} (f : Arrow (Obj W n))
    (i j k : Fin (n.len+1)) (hij : i ≤ j) (hjk : j ≤ k) :
    ExtensionCategory.cof W ((horizontalArrow W i j k hij hjk).map
      ((factorizationOfJointData W J n).inclusion.app f)) :=
  (factorizationOfJointData W J n).cofibration f i j k hij hjk

/-- Its projection is the given base cylinder projection on the original component arrow. -/
theorem factorization_original_projection {n : SimplexCategory} (f : Arrow (Obj W n)) (p : Interval
  n) :
    ((factorizationOfJointData W J n).projection.app f).hom.app p =
      J.projection.app (Arrow.mk (f.hom.hom.app p)) := rfl

include h J in
/-- Actual row App2 simultaneously retains strict factorization, all joint cofibration
conditions, and all original weak target components. -/
theorem actual_row_app2 {n : SimplexCategory} {A : Obj W n} {B : Obj V n}
    (f : (postcompose W V hF n).obj A ⟶ B) :
    ∃ (A' : Obj W n) (a : A ⟶ A') (p : (postcompose W V hF n).obj A' ⟶ B),
      (∀ i j k hij hjk, ExtensionCategory.cof W ((horizontalArrow W i j k hij hjk).map a)) ∧
      (∀ q, V.weq (p.hom.app q)) ∧
      (postcompose W V hF n).map a ≫ p = f :=
  (h.row_approximation_of_joint hF J n).lift f

include h J in
/-- Degree zero remains present with a genuine source row and its actual factorization. -/
theorem degree_zero_app2 {A : Obj W (SimplexCategory.mk 0)} {B : Obj V (SimplexCategory.mk 0)}
    (f : (postcompose W V hF (SimplexCategory.mk 0)).obj A ⟶ B) :
    ∃ (A' : Obj W (SimplexCategory.mk 0)) (a : A ⟶ A')
      (p : (postcompose W V hF (SimplexCategory.mk 0)).obj A' ⟶ B),
      cof W _ a ∧ weq V _ p ∧ (postcompose W V hF _).map a ≫ p = f :=
  (h.row_approximation_of_joint hF J _).lift f

include h J in
/-- App1 reflects the weakness of the unchanged entire original row arrow. -/
theorem original_row_reflection {n : SimplexCategory} {A B : Obj W n} (f : A ⟶ B)
    (hf : weq V n ((postcompose W V hF n).map f)) : weq W n f :=
  (h.row_approximation_of_joint hF J n).reflects f hf

end ApproximationRowsConsumers
