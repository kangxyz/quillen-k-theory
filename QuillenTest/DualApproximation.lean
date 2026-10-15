/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Quillen.Waldhausen.Approximation.Dual
public import Quillen.Waldhausen.Duality.ExactCategory
public import Quillen.Waldhausen.WeakArrow.DualStructure
public import Quillen.Waldhausen.WeakArrow.KEquivalence

/-! Behavioral consumers of actual dual squares, original diagrams and original K-maps. -/
@[expose] public section

open Quillen.Waldhausen


open CategoryTheory.ExactCategory


noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u v
namespace QuillenTest.DualApproximation

open Quillen
open Waldhausen
section OriginalFunctor
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {Wd : Structure Cᵒᵖ} {V : Structure D} {Vd : Structure Dᵒᵖ}
  (hW : IsCompatibleDual W Wd) (hV : IsCompatibleDual V Vd) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hFd : IsExact Wd.cof Wd.weq Vd.cof Vd.weq F.op)
  (h : HasDualApproximationProperty W V Wd.cof.unop F)
  [V.weq.HasTwoOutOfThreeProperty]
  (Jd : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl Wd))

include hW hV h in
omit [V.weq.HasTwoOutOfThreeProperty] in
/-- Opposite App2 still gives the literal original incoming triangle. -/
theorem original_incoming_triangle {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    ∃ (X' : C) (i : X' ⟶ X) (p : Y ⟶ F.obj X'),
      Wd.cof i.op ∧ V.weq p ∧ p ≫ F.map i = f := by
  obtain ⟨X',i,p,hi,hp,he⟩ := (h.op hW hV).lift f.op
  exact ⟨X'.unop, i.unop, p.unop, hi, (hV.weak p.unop).mpr hp,
    congrArg Quiver.Hom.unop he⟩

include hW hV hFd h Jd in
/-- Every original target K-class has exactly one original preimage in every degree. -/
theorem original_K_unique_preimage (n : ℕ) (a : V.K n) :
    ∃! b, KMap hF n b = a :=
  (KMap_bijective_of_dualApproximation hW hV hF hFd h Jd n).existsUnique a

include hW hV hFd h Jd in
/-- Component surjectivity is on the original realization, including degree zero. -/
theorem original_component_preimage (y : V.Delooping) :
    ∃ x, Joined (deloopingMap hF x) y :=
  (deloopingMap_isWeakHomotopyEquivalence_of_dualApproximation hW hV hF hFd h
    Jd).component_surjective y

/-- Grid reversal uses the original opposite arrow diagram at each actual coordinate. -/
theorem original_reversed_coordinate (n : SimplexCategoryᵒᵖ)
    (A : (sSet W.cof W.weq).op.obj n) (t i j) (hij : i ≤ j) :
    ((DualSConstruction.sSetIso hW).hom.app n A).val.obj (grid t i j hij) =
      op (A.val.obj (grid t.rev j.rev i.rev (Fin.rev_le_rev.mpr hij))) := rfl

omit [V.weq.HasTwoOutOfThreeProperty] in
/-- The full simplicial square retains both original functors, not merely their homotopy classes. -/
theorem original_reversal_square :
    SSet.opFunctor.map (sSetMap hF) ≫ (DualSConstruction.sSetIso hV).hom =
      (DualSConstruction.sSetIso hW).hom ≫ sSetMap hFd :=
  DualSConstruction.sSetIso_naturality hW hV hF hFd
end OriginalFunctor

/-- Any actual admissible zero cofiber square is its original kernel square. -/
theorem original_exact_kernel {C : Type u} [Category.{v} C] [Preadditive C]
    [HasFiniteBiproducts C] (E : ExactStructure C) {A B Z Q : C}
    {i : A ⟶ B} {z : A ⟶ Z} {q : B ⟶ Q} {s : Z ⟶ Q}
    (hZ : IsZero Z) (hi : E.inflation i) (hp : IsPushout i z q s) :
    E.deflation q ∧ IsPullback i z q s :=
  E.deflation_pullback_of_inflation_pushout_zero hZ hi hp

section WeakArrow
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) (Vd : Structure Cᵒᵖ) (Wd : Structure Dᵒᵖ)
  (F : C ⥤ D) (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hFd : IsExact Vd.cof Vd.weq Wd.cof Wd.weq F.op)
  (hW : IsCompatibleDual W Wd) (hV : IsCompatibleDual V Vd)

/-- Fibration detection tests the two literal stored arrows of the original comma map. -/
theorem original_weak_arrow_fibrations {X Y : WeakArrow.Obj W F} (f : X ⟶ Y) :
    (WeakArrow.dualWaldhausenStructure V W Vd Wd F hF hFd hW).cof f.op ↔
      Vd.cof f.hom.left.op ∧ Wd.cof f.hom.right.op := Iff.rfl

include hV hFd hW in
/-- Actual original weak-arrow cofiber squares are actual original pullback squares. -/
theorem original_weak_arrow_kernel {A B Z Q : WeakArrow.Obj W F}
    {i : A ⟶ B} {z : A ⟶ Z} {q : B ⟶ Q} {s : Z ⟶ Q}
    (hZ : IsZero Z) (hi : (WeakArrow.waldhausenStructure V W F hF).cof i)
    (hp : IsPushout i z q s) : IsPullback i z q s :=
  ((WeakArrow.dual_compatible V W Vd Wd F hF hFd hW hV).cofiber i z q s hZ).mp ⟨hi,hp⟩ |>.2

/-- The unchanged target projection preserves every actual opposite fibration pushout. -/
theorem original_target_dual_pushout {A B E Q : (WeakArrow.Obj W F)ᵒᵖ}
    {i : A ⟶ B} {f : A ⟶ E} {g : B ⟶ Q} {j : E ⟶ Q}
    (hi : (WeakArrow.dualWaldhausenStructure V W Vd Wd F hF hFd hW).cof i)
    (hp : IsPushout i f g j) :
    IsPushout i.unop.hom.right.op f.unop.hom.right.op g.unop.hom.right.op j.unop.hom.right.op :=
  (WeakArrow.dual_target_exact V W Vd Wd F hF hFd hW).pushout hi hp
end WeakArrow

/-- The genuine first-leg inverse and dual second-leg approximation prove bijectivity
of the unchanged original functor K-map; no intermediate K-equivalence is assumed. -/
theorem original_functor_via_weak_arrow
    {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
    (V : Structure C) (W : Structure D) (Vd : Structure Cᵒᵖ) (Wd : Structure Dᵒᵖ)
    (F : C ⥤ D) (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hFd : IsExact Vd.cof Vd.weq Wd.cof Wd.weq F.op)
    (hW : IsCompatibleDual W Wd) (hV : IsCompatibleDual V Vd)
    [W.weq.HasTwoOutOfThreeProperty]
    (h : HasDualApproximationProperty (WeakArrow.waldhausenStructure V W F hF) W
      (WeakArrow.dualWaldhausenStructure V W Vd Wd F hF hFd hW).cof.unop (WeakArrow.target W F))
    (Jd : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl
      (WeakArrow.dualWaldhausenStructure V W Vd Wd F hF hFd hW))) (n : ℕ) :
    Function.Bijective (KMap hF n) :=
  (WeakArrow.KMap_bijective_iff_target V W F hF n).mpr
    (KMap_bijective_of_dualApproximation
      (WeakArrow.dual_compatible V W Vd Wd F hF hFd hW hV) hW
      (WeakArrow.target_exact V W F hF) (WeakArrow.dual_target_exact V W Vd Wd F hF hFd hW)
      h Jd n)

end QuillenTest.DualApproximation
