/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.Realization.Edgewise
public import Quillen.Topology.Realization.HomotopyBridge
public import Mathlib.Topology.Homotopy.Contractible

/-! Explicit contraction of the edgewise subdivision of every representable. -/
@[expose] public section

noncomputable section
open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Edgewise

/-- Increasing maps from the two halves glue if all first-half values precede
all second-half values. -/
def joinDesc {p q r : SimplexCategory} (a : p ⟶ r) (b : q ⟶ r)
    (h : ∀ i j, a.toOrderHom i ≤ b.toOrderHom j) : joinObj p q ⟶ r :=
  SimplexCategory.Hom.mk {
    toFun i := if hi : i.val < p.len + 1 then a.toOrderHom ⟨i.val, hi⟩
      else b.toOrderHom ⟨i.val - (p.len + 1), by
        have := i.isLt; dsimp [joinObj] at this; omega⟩
    monotone' := by
      intro i j hij
      dsimp only
      split_ifs with hi hj hj
      · exact a.toOrderHom.monotone hij
      · exact h _ _
      · have : i.val ≤ j.val := hij; omega
      · exact b.toOrderHom.monotone (Nat.sub_le_sub_right hij _) }

@[simp] theorem joinDesc_left {p q r : SimplexCategory} (a : p ⟶ r) (b : q ⟶ r)
    (h : ∀ i j, a.toOrderHom i ≤ b.toOrderHom j) (i : Fin (p.len + 1)) :
    (joinDesc a b h).toOrderHom ((left p q).toOrderHom i) = a.toOrderHom i := by
  change (if hi : i.val < p.len + 1 then _ else _) = _
  rw [dite_eq_left i.isLt]
  rfl

@[simp] theorem joinDesc_right {p q r : SimplexCategory} (a : p ⟶ r) (b : q ⟶ r)
    (h : ∀ i j, a.toOrderHom i ≤ b.toOrderHom j) (i : Fin (q.len + 1)) :
    (joinDesc a b h).toOrderHom ((right p q).toOrderHom i) = b.toOrderHom i := by
  change (if hi : p.len + 1 + i.val < p.len + 1 then _ else _) = _
  rw [dite_eq_right (by omega)]
  congr 1
  apply Fin.ext
  change p.len + 1 + i.val - (p.len + 1) = i.val
  omega

/-- Decrease first-half endpoints toward zero along a simplicial interval. -/
def contractLeft {p r : SimplexCategory} (s : ε.obj p ⟶ r) (t : p ⟶ ⦋1⦌) : p ⟶ r :=
  SimplexCategory.Hom.mk {
    toFun i := if t.toOrderHom i.rev = 0 then s.toOrderHom ((left p p).toOrderHom i) else 0
    monotone' := by
      intro i j hij
      dsimp only
      split_ifs with hi hj hj
      · exact s.toOrderHom.monotone ((left p p).toOrderHom.monotone hij)
      · have ht := t.toOrderHom.monotone (Fin.rev_le_rev.mpr hij)
        rw [hi] at ht
        exact (hj (le_antisymm ht (Fin.zero_le _))).elim
      · exact Fin.zero_le _
      · exact le_rfl }

/-- Increase second-half endpoints toward the last vertex. -/
def contractRight {p r : SimplexCategory} (s : ε.obj p ⟶ r) (t : p ⟶ ⦋1⦌) : p ⟶ r :=
  SimplexCategory.Hom.mk {
    toFun i := if t.toOrderHom i = 0 then s.toOrderHom ((right p p).toOrderHom i) else Fin.last
      r.len
    monotone' := by
      intro i j hij
      dsimp only
      split_ifs with hi hj hj
      · exact s.toOrderHom.monotone ((right p p).toOrderHom.monotone hij)
      · exact Fin.le_last _
      · have ht := t.toOrderHom.monotone hij
        rw [hj] at ht
        exact (hi (le_antisymm ht (Fin.zero_le _))).elim
      · exact le_rfl }

/-- The all-degree contraction of an interval-valued simplex toward `(0,n)`. -/
def contractOperator {p r : SimplexCategory} (s : ε.obj p ⟶ r) (t : p ⟶ ⦋1⦌) :
    ε.obj p ⟶ r :=
  joinDesc (contractLeft s t) (contractRight s t) (by
    intro i j
    change (if t.toOrderHom i.rev = 0 then _ else _) ≤
      (if t.toOrderHom j = 0 then _ else _)
    split_ifs
    · apply s.toOrderHom.monotone
      change i.val ≤ p.len + 1 + j.val
      omega
    · exact Fin.le_last _
    · exact Fin.zero_le _
    · exact Fin.zero_le _)

@[simp] theorem contractOperator_left {p r : SimplexCategory}
    (s : ε.obj p ⟶ r) (t : p ⟶ ⦋1⦌) (i : Fin (p.len + 1)) :
    (contractOperator s t).toOrderHom ((left p p).toOrderHom i) =
      if t.toOrderHom i.rev = 0 then s.toOrderHom ((left p p).toOrderHom i) else 0 :=
  joinDesc_left _ _ _ _

@[simp] theorem contractOperator_right {p r : SimplexCategory}
    (s : ε.obj p ⟶ r) (t : p ⟶ ⦋1⦌) (i : Fin (p.len + 1)) :
    (contractOperator s t).toOrderHom ((right p p).toOrderHom i) =
      if t.toOrderHom i = 0 then s.toOrderHom ((right p p).toOrderHom i) else Fin.last r.len :=
  joinDesc_right _ _ _ _

@[simp] theorem ε_map_left {p q : SimplexCategory} (f : p ⟶ q)
    (i : Fin (p.len + 1)) :
    (ε.map f).toOrderHom ((left p p).toOrderHom i) =
      (left q q).toOrderHom ((f.toOrderHom i.rev).rev) :=
  joinMap_left (SimplexCategory.rev.map f) f i

@[simp] theorem ε_map_right {p q : SimplexCategory} (f : p ⟶ q)
    (i : Fin (p.len + 1)) :
    (ε.map f).toOrderHom ((right p p).toOrderHom i) =
      (right q q).toOrderHom (f.toOrderHom i) :=
  joinMap_right (SimplexCategory.rev.map f) f i

/-- The contraction commutes with every simplicial operator, including
operators that do not preserve either endpoint. -/
theorem contractOperator_naturality {p q r : SimplexCategory}
    (f : p ⟶ q) (s : ε.obj q ⟶ r) (t : q ⟶ ⦋1⦌) :
    contractOperator (ε.map f ≫ s) (f ≫ t) = ε.map f ≫ contractOperator s t := by
  ext i : 3
  rcases join_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      contractOperator_left, ε_map_left, Fin.rev_rev]
  · simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      contractOperator_right, ε_map_right]

/-- A simplicial cylinder contracts the subdivision of a standard simplex. -/
def simplexCylinder (n : ℕ) : subdivision (Δ[n] : SSet.{u}) ⊗ Δ[1] ⟶
    subdivision (Δ[n] : SSet.{u}) where
  app p := ↾fun z ↦ ULift.up (contractOperator z.1.down z.2.down)
  naturality p q f := by
    ext z : 3
    exact congrArg ULift.up (contractOperator_naturality f.unop z.1.down z.2.down)

/-- The distinguished interval `(0,n)` is a vertex of the subdivided simplex. -/
def simplexVertex (n : ℕ) : subdivision (Δ[n] : SSet.{u}) _⦋0⦌ :=
  ULift.up (joinDesc (⦋0⦌.const ⦋n⦌ 0) (⦋0⦌.const ⦋n⦌ (Fin.last n))
    (fun _ _ ↦ Fin.zero_le _))

@[simp] theorem simplexCylinder_zero (n : ℕ) :
    SSet.ι₀ ≫ simplexCylinder.{u} n = 𝟙 _ := by
  ext p s
  apply congrArg ULift.up
  change contractOperator s.down (p.unop.const ⦋1⦌ 0) = s.down
  ext i : 3
  rcases join_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    simp [contractOperator_left, contractOperator_right]

@[simp] theorem simplexCylinder_one (n : ℕ) :
    SSet.ι₁ ≫ simplexCylinder.{u} n = SSet.const (simplexVertex n) := by
  ext p s
  apply congrArg ULift.up
  change contractOperator s.down (p.unop.const ⦋1⦌ 1) =
    ε.map (p.unop.const ⦋0⦌ 0) ≫ (simplexVertex.{u} n).down
  ext i : 3
  rcases join_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    simp [contractOperator_left, contractOperator_right, simplexVertex,
      SimplexCategory.comp_toOrderHom, ε_map_left, ε_map_right] <;> rfl

/-- An explicit simplicial contraction of the subdivided standard simplex. -/
def simplexContraction (n : ℕ) :
    SSet.Homotopy (𝟙 (subdivision (Δ[n] : SSet.{u}))) (SSet.const (simplexVertex n)) where
  h := simplexCylinder n
  h₀ := simplexCylinder_zero n
  h₁ := simplexCylinder_one n
  rel := by
    ext p z
    exact z.1.property.elim

/-- The actual geometric realization of an edgewise-subdivided simplex is contractible. -/
theorem contractibleSpace_simplex (n : ℕ) : ContractibleSpace |subdivision (Δ[n] : SSet.{u})| := by
  apply (contractible_iff_id_nullhomotopic _).2
  refine ⟨realizationPoint (simplexVertex n), ?_⟩
  have h := realizationSimplicialHomotopy (simplexContraction.{u} n)
  have hc : (SSet.toTop.map (SSet.const (X := subdivision (Δ[n] : SSet.{u})) (simplexVertex.{u}
    n))).hom =
      ContinuousMap.const _ (realizationPoint (simplexVertex n)) := by
    ext x
    exact realization_const_apply _ x
  rw [SSet.toTop.map_id, hc] at h
  exact ⟨h⟩

end Quillen.Edgewise
