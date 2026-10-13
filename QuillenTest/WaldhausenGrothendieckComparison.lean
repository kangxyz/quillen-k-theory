/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.ObjectCompatibility

/-! Consumers retain original object loops, weak arrows, cofiber pushouts and
arbitrary fine K₀ classes, without any factorization or presentation assumption. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen.Waldhausen
universe u
namespace QuillenTest.WaldhausenGrothendieckComparison

open Quillen
variable {C D G : Type u} [SmallCategory C] [SmallCategory D] [AddCommGroup G]
  (W : Structure C) (V : Structure D)

/-- An original additive invariant can separate actual original homotopical object loops. -/
theorem grading_separates_object_loops (d : Cofinality.Grading W G) (A B : C)
    (h : d.value A ≠ d.value B) : W.kZeroObjectClass A ≠ W.kZeroObjectClass B := by
  intro he
  apply h
  apply Multiplicative.ofAdd.injective
  have hm := congrArg d.fineKZeroMap he
  simpa only [d.fineKZeroMap_objectClass] using hm

/-- Original weak arrows identify the images of the original topological object classes. -/
theorem weak_arrow_classical_images {A B : C} (f : A ⟶ B) (hf : W.weq f) :
    AlgebraicGrothendieck.kZeroToGrothendieck W (W.kZeroObjectClass A) =
      AlgebraicGrothendieck.kZeroToGrothendieck W (W.kZeroObjectClass B) := by
  simp only [AlgebraicGrothendieck.kZeroToGrothendieck_objectClass]
  exact congrArg Multiplicative.ofAdd (AlgebraicGrothendieck.objectClass_weak W f hf)

/-- The actual displayed cofiber is the difference of the original endpoint classes
under the genuine fine homotopical-to-classical map. -/
theorem original_cofiber_difference {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : W.cof i) (hQ : IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q)) :
    AlgebraicGrothendieck.kZeroToGrothendieck W
      (W.kZeroObjectClass B * (W.kZeroObjectClass A)⁻¹) =
        Multiplicative.ofAdd (AlgebraicGrothendieck.objectClass W Q) := by
  simp only [map_mul, map_inv, AlgebraicGrothendieck.kZeroToGrothendieck_objectClass]
  exact congrArg Multiplicative.ofAdd ((AlgebraicGrothendieck.grading W).cofiber_value hi hQ).symm

/-- Naturality holds on an arbitrary original fine homotopical K₀ class. -/
theorem original_exact_functor_naturality (F : C ⥤ D)
    (hF : IsExact W.cof W.weq V.cof V.weq F) (x : W.K 0) :
    AlgebraicGrothendieck.kZeroToGrothendieck V (KMap hF 0 x) =
      (AlgebraicGrothendieck.map W F hF).toMultiplicative
        (AlgebraicGrothendieck.kZeroToGrothendieck W x) :=
  (AlgebraicGrothendieck.kZeroToGrothendieck_natural W V F hF x).symm

/-- Every classical element is represented by a genuine fine K₀ class without a
hypothesis that one individual original object represents that element. -/
theorem every_classical_class_is_attained (a : AlgebraicGrothendieck.Group W) :
    ∃ x : W.K 0, AlgebraicGrothendieck.kZeroToGrothendieck W x = Multiplicative.ofAdd a :=
  AlgebraicGrothendieck.kZeroToGrothendieck_surjective W (Multiplicative.ofAdd a)

end QuillenTest.WaldhausenGrothendieckComparison
