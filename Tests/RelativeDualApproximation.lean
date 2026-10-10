/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Approximation.DualInverseImage
import Quillen.Waldhausen.WeakArrow.RelativeKEquivalence

/-! # Semantic consumers of actual relative dual approximation -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Quillen.Waldhausen
universe u v
namespace Tests.RelativeDualApproximation
section Lift
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {W : Structure C} {Wd : Structure Cᵒᵖ} {V : Structure D} {Vd : Structure Dᵒᵖ}
  {U : Structure E} {Ud : Structure Eᵒᵖ}
  (hW : IsCompatibleDual W Wd) (hV : IsCompatibleDual V Vd)
  (hU : IsCompatibleDual U Ud) {F : C ⥤ D} {G : D ⥤ E}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hFd : IsExact Wd.cof Wd.weq Vd.cof Vd.weq F.op)
  (hG : IsExact V.cof V.weq U.cof U.weq G)
  (hGd : IsExact Vd.cof Vd.weq Ud.cof Ud.weq G.op)
  (h : HasDualApproximationProperty W V Wd.cof.unop F)

include h hF hG in
/-- Actual incoming factors still solve the original equation after weak enlargement. -/
theorem actual_relative_lift {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    ∃ (X' : C) (i : X' ⟶ X) (p : Y ⟶ F.obj X'),
      Wd.cof i.op ∧ U.weq (G.map p) ∧ p ≫ F.map i = f :=
  (h.inverseImageComposite hF hG).lift f

include hW hV hU hFd hGd h in
/-- The complete original relative map gives a unique preimage already in degree zero. -/
theorem unique_original_relative_preimage [U.weq.HasTwoOutOfThreeProperty]
    (J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl Wd))
    (y : (Structure.withInverseImageWeak hG).K 0) :
    ∃! x, KMap (inverseImageComposite_exact hF hG) 0 x = y := by
  obtain ⟨hi, hs⟩ := KMap_bijective_of_dualApproximation_inverseImage
    hW hV hU hF hFd hG hGd h J 0
  obtain ⟨x, hx⟩ := hs y
  exact ⟨x, hx, fun z hz => hi (hz.trans hx.symm)⟩

/-- Coarse retargeting has the same actual left endpoint and projection composite. -/
theorem unchanged_joint_factorization
    (J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl Wd))
    (N : Fibration.NestedWeakEquivalences Wd) [N.coarse.weq.HasTwoOutOfThreeProperty]
    (f : Arrow Cᵒᵖ) :
    (J.toCoarse N).inl.app f ≫ ((J.toCoarse N).joint.obj f).obj.hom ≫
      (J.toCoarse N).projection.app f = f.hom :=
  (J.toCoarse N).factorization f
end Lift

section FirstLeg
variable {C D E : Type (max u v)} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  (V : Structure C) (W : Structure D) (U : Structure E)
  (F : C ⥤ D) (G : D ⥤ E)
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact W.cof W.weq U.cof U.weq G)
  [U.weq.HasTwoOutOfThreeProperty]

/-- Fine global weak-arrow objects are retained even when map weakness is enlarged. -/
theorem stored_arrow_still_globally_weak (X : WeakArrow.Obj W F) : W.weq X.obj.hom :=
  X.property

include V hF hG in
/-- The relative source component is controlled by the actual original target square. -/
theorem actual_source_component {X Y : WeakArrow.Obj W F} (f : X ⟶ Y)
    (hf : U.weq (G.map f.hom.right)) : U.weq (G.map (F.map f.hom.left)) :=
  (WeakArrow.Relative.source_exact V W U F G hF hG).weak f hf

/-- The inverse recovers every actual relative weak-arrow K-class, including K₀. -/
theorem actual_first_leg_inverse (n : ℕ)
    (x : (WeakArrow.Relative.arrowStructure V W U F G hF hG).K n) :
    KMap (WeakArrow.Relative.diagonal_exact V W U F G hF hG) n
      (KMap (WeakArrow.Relative.source_exact V W U F G hF hG) n x) = x :=
  WeakArrow.Relative.KMap_diagonal_source V W U F G hF hG n x

/-- The actual target and diagonal composite is the unchanged original relative map. -/
theorem original_relative_factorization (n : ℕ)
    (x : (WeakArrow.Relative.sourceStructure V W U F G hF hG).K n) :
    KMap (WeakArrow.Relative.target_exact V W U F G hF hG) n
      (KMap (WeakArrow.Relative.diagonal_exact V W U F G hF hG) n x) =
      KMap (WeakArrow.Relative.functor_exact V W U F G hF hG) n x :=
  DFunLike.congr_fun (WeakArrow.Relative.KMap_factor V W U F G hF hG n) x
end FirstLeg
end Tests.RelativeDualApproximation
