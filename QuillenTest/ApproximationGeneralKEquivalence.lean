/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Approximation.GeneralKEquivalence

/-! Actual-map and genuinely different-universe consumers for approximation transport. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace SmallModelApproximationConsumers
open Quillen Quillen.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W))

include h in
/-- Small-model App2 retains actual original source factors and their exact up-mapped equation. -/
theorem original_smallModel_factors {X : SmallModel C} {Y : SmallModel D}
    (f : (smallModelFunctor F).obj X ⟶ Y) :
    ∃ (X' : C) (i : AsSmall.down.obj X ⟶ X') (p : F.obj X' ⟶ AsSmall.down.obj Y),
      W.cof i ∧ V.weq p ∧
      (smallModelFunctor F).map ((AsSmall.up : C ⥤ SmallModel C).map i) ≫
        (AsSmall.up : D ⥤ SmallModel D).map p = f := by
  obtain ⟨X', i, p, hi, hp, he⟩ := h.lift (AsSmall.down.map f)
  exact ⟨X', i, p, hi, hp, congrArg (AsSmall.up : D ⥤ SmallModel D).map he⟩

/-- The transported projection is the actual original base projection, lifted literally. -/
theorem transported_joint_projection (f : Arrow C) :
    J.reflexiveSmallModel.projection.app ((AsSmall.up : C ⥤ SmallModel C).mapArrow.obj f) =
      (AsSmall.up : C ⥤ SmallModel C).map (J.projection.app f) := rfl

/-- The transported first endpoint is likewise the original endpoint inclusion. -/
theorem transported_joint_first_endpoint (f : Arrow C) :
    J.reflexiveSmallModel.inl.app ((AsSmall.up : C ⥤ SmallModel C).mapArrow.obj f) =
      (AsSmall.up : C ⥤ SmallModel C).map (J.inl.app f) := rfl

variable [V.weq.HasTwoOutOfThreeProperty]

include h J in
/-- Arbitrary object/hom universes still give source points for all original target components. -/
theorem original_component_surjective (y : V.Delooping) :
    ∃ x, Joined (deloopingMap hF x) y :=
  (h.deloopingMap_isWeakHomotopyEquivalence_general hF J).component_surjective y

include h J in
/-- Every canonical original K-zero class has a unique actual source class. -/
theorem original_K_zero_unique_preimage (y : V.K 0) : ∃! x, KMap hF 0 x = y := by
  obtain ⟨x, hx⟩ := (h.KMap_bijective_general hF J 0).surjective y
  exact ⟨x, hx, fun z hz ↦ (h.KMap_bijective_general hF J 0).injective (hz.trans hx.symm)⟩

/-- The general approximation equivalence agrees with the small one through the
existing natural small-model K-equivalences, including canonical rebasing. -/
theorem original_small_K_square (n : ℕ) (x : W.K n) :
    V.smallModelKEquiv n (h.KEquivGeneral hF J n x) =
      h.smallModel.KEquiv hF.smallModel J.reflexiveSmallModel n (W.smallModelKEquiv n x) :=
  congrArg (fun k ↦ k x) (smallModelKEquiv_naturality hF n)

end SmallModelApproximationConsumers

namespace LargerObjectApproximationConsumer
open Quillen Quillen.Waldhausen
variable {C D : Type (u+1)} [Category.{u} C] [Category.{u} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty]
  (J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W))
include h J

/-- The category is genuinely large relative to its morphism universe. -/
theorem original_KMap_bijective (n : ℕ) : Function.Bijective (KMap hF n) :=
  h.KMap_bijective_general hF J n

end LargerObjectApproximationConsumer

namespace LargerHomApproximationConsumer
open Quillen Quillen.Waldhausen
variable {C D : Type u} [Category.{u+1} C] [Category.{u+1} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty]
  (J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W))
include h J

/-- The morphism universe may also be genuinely larger than the object universe. -/
theorem original_KMap_bijective (n : ℕ) : Function.Bijective (KMap hF n) :=
  h.KMap_bijective_general hF J n

end LargerHomApproximationConsumer
