/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.Functoriality
public import Quillen.Waldhausen.Fibration.AllWeak.RelativeContractible
public import Quillen.Waldhausen.Fibration.AllWeak.TotalFiberSquare
public import Quillen.Waldhausen.Fibration.RelativeRows.WeakTotalFiber

/-!
# The literal first S-cylinder in the actual relative total

For a small Waldhausen category, the original one-row insertion cylinder lifts to the
all-weak relative total by adding an initial zero vertex. Its tail is exactly the original
suspension cylinder, and its faces are the literal zero map and original total-fiber inclusion.
All exactness and acyclicity witnesses are proved for those original functors.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS
open Fibration Fibration.RelativeRows
variable {C : Type u} [SmallCategory C] (W : Structure C)

/-- Extend the actual time parameter by the new initial zero vertex. -/
def relativeTime {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) : addInitial.obj n ⟶ ⦋1⦌ :=
  SimplexCategory.Hom.mk {
    toFun := Fin.cases 0 τ.toOrderHom
    monotone' := by
      intro i j h
      cases i using Fin.cases with
      | zero => exact Fin.zero_le _
      | succ i =>
        cases j using Fin.cases with
        | zero => have h' : i.val + 1 ≤ 0 := h; omega
        | succ j => exact τ.toOrderHom.monotone (Nat.le_of_succ_le_succ h) }

lemma relativeTime_reindex {m n : SimplexCategory} (α : m ⟶ n) (τ : n ⟶ ⦋1⦌) :
    addInitial.map α ≫ relativeTime τ = relativeTime (α ≫ τ) := by
  ext i : 3
  cases i using Fin.cases <;> rfl

lemma relativeTime_tail {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    tail.app n ≫ relativeTime τ = τ := by ext i : 3; rfl

lemma relativeTime_zero (n : SimplexCategory) :
    relativeTime (n.const ⦋1⦌ 0) = (addInitial.obj n).const ⦋1⦌ 0 := by
  ext i : 3
  cases i using Fin.cases <;> rfl

lemma relativeTime_one (n : SimplexCategory) :
    relativeTime (n.const ⦋1⦌ 1) = fiberOrdinal n := rfl

/-- The actual one-row time construction, with honest all-weak acyclicity witnesses. -/
def relativeTimeRow {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) : C ⥤ RelativeRows.Obj (AllWeak.nested
    W) n :=
  (RelativeRows.objects (AllWeak.nested W) n).lift (suspensionRow W (relativeTime τ))
    (fun _ _ ↦ AllWeak.acyclic W _)

lemma relativeTimeRow_exact {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    IsExact W.cof W.weq (RelativeRows.waldhausenStructure (AllWeak.nested W) n).cof
      (RelativeRows.waldhausenStructure (AllWeak.nested W) n).weq (relativeTimeRow W τ) where
  zero h := IsZero.of_full_of_faithful_of_isZero (RelativeRows.forget (AllWeak.nested W) n) _
    ((suspensionRow_exact W (relativeTime τ)).zero h)
  cofibration f hf := (suspensionRow_exact W (relativeTime τ)).cofibration f hf
  weak f hf := (suspensionRow_exact W (relativeTime τ)).weak f hf
  pushout hf h := IsPushout.of_map_of_faithful (RelativeRows.forget (AllWeak.nested W) n)
    ((suspensionRow_exact W (relativeTime τ)).pushout hf h)

lemma relativeTimeRow_reindex {m n : SimplexCategory} (α : m ⟶ n) (τ : n ⟶ ⦋1⦌) :
    relativeTimeRow W τ ⋙ RelativeRows.reindex (AllWeak.nested W) α =
      relativeTimeRow W (α ≫ τ) := by
  apply RelativeRows.functor_eq_of_comp_forget (AllWeak.nested W)
  change suspensionRow W (relativeTime τ) ⋙ QuotientRows.reindex W (addInitial.map α) =
    suspensionRow W (relativeTime (α ≫ τ))
  rw [← suspensionRow_reindex, relativeTime_reindex]

/-- The original suspension cylinder lifts to the actual contractible relative total. -/
def relativeCylinder : sSet W.cof W.weq ⊗ Δ[1] ⟶
    TheoremA.diagonalSSet (relativeSRows (AllWeak.nested W)) where
  app n := ↾fun z ↦ ⟨z.1.val ⋙ relativeTimeRow W z.2.down,
    z.1.property.postcomp (relativeTimeRow_exact W z.2.down)⟩
  naturality n m α := by
    ext z : 3
    apply Subtype.ext
    change (gridMap α.unop ⋙ z.1.val) ⋙ relativeTimeRow W (α.unop ≫ z.2.down) =
      (gridMap α.unop ⋙ z.1.val) ⋙ relativeTimeRow W z.2.down ⋙ RelativeRows.reindex
        (AllWeak.nested W) α.unop
    rw [relativeTimeRow_reindex]

/-- The original acyclic-tail projection followed by the original witness-forgetting iso. -/
def relativeTail : TheoremA.diagonalSSet (relativeSRows (AllWeak.nested W)) ⟶ doubleDiagonal W :=
  TheoremA.diagonalMap (tailSRows (AllWeak.nested W)) ≫ (AllWeak.ordinaryDiagonalIso W).hom

lemma relativeCylinder_tail : relativeCylinder W ≫ relativeTail W = suspensionCylinder W := by
  ext n z : 4
  apply Subtype.ext
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

lemma relativeTimeRow_zero (n : SimplexCategory) :
    relativeTimeRow W (n.const ⦋1⦌ 0) =
      (Functor.const C).obj (RelativeRows.zero (AllWeak.nested W) n) := by
  apply RelativeRows.functor_eq_of_comp_forget (AllWeak.nested W)
  change suspensionRow W (relativeTime (n.const ⦋1⦌ 0)) = _
  rw [relativeTime_zero, suspensionRow_const]
  rfl

lemma relativeTimeRow_one (n : SimplexCategory) :
    relativeTimeRow W (n.const ⦋1⦌ 1) = fiber (AllWeak.nested W) n := rfl

lemma relativeCylinder_zero : SSet.ι₀ ≫ relativeCylinder W =
    SSet.const (totalZeroVertex (AllWeak.nested W)) := by
  ext n z : 4
  apply Subtype.ext
  change z.val ⋙ relativeTimeRow W (n.unop.const ⦋1⦌ 0) = _
  rw [relativeTimeRow_zero]
  rfl

lemma relativeCylinder_one : SSet.ι₁ ≫ relativeCylinder W = totalFiberInclusion (AllWeak.nested
    W) := by
  ext n z : 4
  apply Subtype.ext
  rfl

/-- The lifted original cylinder joins the literal zero to the original split-fiber map. -/
def relativeHomotopy : SSet.Homotopy (SSet.const (X := sSet W.cof W.weq)
    (totalZeroVertex (AllWeak.nested W))) (totalFiberInclusion (AllWeak.nested W)) where
  h := relativeCylinder W
  h₀ := relativeCylinder_zero W
  h₁ := relativeCylinder_one W
  rel := by ext n z; exact z.1.property.elim

end Quillen.Waldhausen.IteratedS
