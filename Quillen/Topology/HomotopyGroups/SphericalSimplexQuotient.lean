/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Cube.StickBreaking
public import Quillen.Topology.HomotopyGroups.SphericalSimplex

/-!
# Spherical-simplex representation by the explicit cube quotient

The stick-breaking map is not treated as a homeomorphism. Its proved quotient
property and boundary fibres give descent of actual boundary-constant cubes
and time-preserving relative homotopies. The resulting class belongs to the
existing cubical homotopy group. No signed boundary-addition theorem is assumed
or asserted here.
-/

@[expose] public section

open Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Convexity
open scoped Topology unitInterval
universe u

namespace Quillen.SphericalSimplex
variable {Z : Type u} [TopologicalSpace Z] {z : Z} {n : ℕ}

/-- Pull a spherical simplex back along the explicit ordered cube quotient. -/
def toGenLoopStick (f : SphericalSimplex Z z n) : GenLoop (Fin n) Z z :=
  ⟨f.val.comp (Cube.stickBreakingMap n), fun t ht ↦
    f.property _ ((Cube.stickBreaking_mem_boundary_iff n t).mpr ht)⟩

@[simp] theorem toGenLoopStick_apply (f : SphericalSimplex Z z n) (t : Fin n → I) :
    f.toGenLoopStick t = f (Cube.stickBreaking n t) := rfl

/-- The original basedness condition makes every cube constant on every quotient fibre. -/
theorem genLoop_factorsThrough_stick (p : GenLoop (Fin n) Z z) :
    Function.FactorsThrough p.val (Cube.stickBreakingMap n) := by
  intro t u h
  rcases Cube.stickBreaking_fibre_boundary h with h | ⟨ht, hu⟩
  · exact congrArg p h
  · exact (p.property t ht).trans (p.property u hu).symm

/-- Quotient descent of the actual cube, not precomposition with a nonexistent inverse. -/
def ofGenLoopStick (p : GenLoop (Fin n) Z z) : SphericalSimplex Z z n :=
  ⟨(Cube.stickBreaking_isQuotientMap n).lift p.val (genLoop_factorsThrough_stick p), by
    intro x hx
    obtain ⟨t, rfl⟩ := Cube.stickBreaking_surjective n x
    have hlift := ContinuousMap.congr_fun
      ((Cube.stickBreaking_isQuotientMap n).lift_comp p.val (genLoop_factorsThrough_stick p)) t
    exact hlift.trans (p.property t ((Cube.stickBreaking_mem_boundary_iff n t).mp hx))⟩

@[simp] theorem ofGenLoopStick_apply_stick (p : GenLoop (Fin n) Z z) (t : Fin n → I) :
    ofGenLoopStick p (Cube.stickBreaking n t) = p t :=
  ContinuousMap.congr_fun
    ((Cube.stickBreaking_isQuotientMap n).lift_comp p.val (genLoop_factorsThrough_stick p)) t

@[simp] theorem toGenLoopStick_ofGenLoopStick (p : GenLoop (Fin n) Z z) :
    (ofGenLoopStick p).toGenLoopStick = p := by ext t; simp

@[simp] theorem ofGenLoopStick_toGenLoopStick (f : SphericalSimplex Z z n) :
    ofGenLoopStick f.toGenLoopStick = f := by
  ext x
  obtain ⟨t, rfl⟩ := Cube.stickBreaking_surjective n x
  simp

/-- The explicit quotient still gives a bijection of boundary-constant representatives. -/
def genLoopStickEquiv : SphericalSimplex Z z n ≃ GenLoop (Fin n) Z z where
  toFun := toGenLoopStick
  invFun := ofGenLoopStick
  left_inv := ofGenLoopStick_toGenLoopStick
  right_inv := toGenLoopStick_ofGenLoopStick

/-- Pull back the full homotopy, leaving its time coordinate untouched. -/
def homotopyToGenLoopStick {f g : SphericalSimplex Z z n}
    (H : f.val.HomotopyRel g.val (simplexBoundary n)) :
    f.toGenLoopStick.val.HomotopyRel g.toGenLoopStick.val (_root_.Cube.boundary (Fin n)) where
  toHomotopy := H.toHomotopy.compContinuousMap (Cube.stickBreakingMap n)
  prop' s t ht := H.eq_fst s ((Cube.stickBreaking_mem_boundary_iff n t).mpr ht)

/-- The product quotient used for time-preserving homotopy descent. -/
def stickCylinderMap (n : ℕ) :
    C(I × (Fin n → I), I × StdSimplex ℝ (Fin (n + 1))) :=
  (ContinuousMap.id I).prodMap (Cube.stickBreakingMap n)

theorem stickCylinderMap_isQuotientMap (n : ℕ) : IsQuotientMap (stickCylinderMap n) := by
  apply IsQuotientMap.of_surjective_continuous ?_ (stickCylinderMap n).continuous
  rintro ⟨s, x⟩
  obtain ⟨t, rfl⟩ := Cube.stickBreaking_surjective n x
  exact ⟨(s, t), rfl⟩

/-- Every relative homotopy is constant on each fibre of the time-preserving quotient. -/
theorem homotopy_factorsThrough_stick {f g : SphericalSimplex Z z n}
    (H : f.toGenLoopStick.val.HomotopyRel g.toGenLoopStick.val
      (_root_.Cube.boundary (Fin n))) :
    Function.FactorsThrough H.toContinuousMap (stickCylinderMap n) := by
  rintro ⟨s, t⟩ ⟨s', u⟩ h
  have hs : s = s' := congrArg Prod.fst h
  have htu : Cube.stickBreaking n t = Cube.stickBreaking n u := congrArg Prod.snd h
  subst s'
  rcases Cube.stickBreaking_fibre_boundary htu with heq | ⟨ht, hu⟩
  · exact congrArg (fun v ↦ H (s, v)) heq
  · exact (H.eq_fst s ht).trans
      ((f.toGenLoopStick.property t ht).trans
        ((f.toGenLoopStick.property u hu).symm.trans (H.eq_fst s hu).symm))

/-- Descend the full boundary-relative homotopy through the compact product quotient. -/
def homotopyFromGenLoopStick {f g : SphericalSimplex Z z n}
    (H : f.toGenLoopStick.val.HomotopyRel g.toGenLoopStick.val
      (_root_.Cube.boundary (Fin n))) : f.val.HomotopyRel g.val (simplexBoundary n) where
  toContinuousMap := (stickCylinderMap_isQuotientMap n).lift H.toContinuousMap
    (homotopy_factorsThrough_stick H)
  map_zero_left x := by
    obtain ⟨t, rfl⟩ := Cube.stickBreaking_surjective n x
    exact (ContinuousMap.congr_fun
      ((stickCylinderMap_isQuotientMap n).lift_comp H.toContinuousMap
        (homotopy_factorsThrough_stick H)) (0, t)).trans (H.apply_zero t)
  map_one_left x := by
    obtain ⟨t, rfl⟩ := Cube.stickBreaking_surjective n x
    exact (ContinuousMap.congr_fun
      ((stickCylinderMap_isQuotientMap n).lift_comp H.toContinuousMap
        (homotopy_factorsThrough_stick H)) (1, t)).trans (H.apply_one t)
  prop' s x hx := by
    obtain ⟨t, rfl⟩ := Cube.stickBreaking_surjective n x
    exact (ContinuousMap.congr_fun
      ((stickCylinderMap_isQuotientMap n).lift_comp H.toContinuousMap
        (homotopy_factorsThrough_stick H)) (s, t)).trans
      (H.eq_fst s ((Cube.stickBreaking_mem_boundary_iff n t).mp hx))

/-- Descent preserves the whole original homotopy track at every time. -/
@[simp] theorem homotopyFromGenLoopStick_apply_stick {f g : SphericalSimplex Z z n}
    (H : f.toGenLoopStick.val.HomotopyRel g.toGenLoopStick.val
      (_root_.Cube.boundary (Fin n))) (s : I) (t : Fin n → I) :
    homotopyFromGenLoopStick H (s, Cube.stickBreaking n t) = H (s, t) :=
  ContinuousMap.congr_fun
    ((stickCylinderMap_isQuotientMap n).lift_comp H.toContinuousMap
      (homotopy_factorsThrough_stick H)) (s, t)

/-- The actual original Pi class defined by the explicit quotient. -/
def homotopyClassStick (f : SphericalSimplex Z z n) : HomotopyGroup.Pi n Z z :=
  Quotient.mk' f.toGenLoopStick

theorem homotopyClassStick_surjective : Function.Surjective
    (homotopyClassStick : SphericalSimplex Z z n → HomotopyGroup.Pi n Z z) := by
  intro a
  refine Quotient.inductionOn a (fun p ↦ ?_)
  refine ⟨ofGenLoopStick p, ?_⟩
  simp only [homotopyClassStick, toGenLoopStick_ofGenLoopStick]
  rfl

/-- Equality of original classes is exactly genuine simplex boundary-relative homotopy. -/
theorem homotopyClassStick_eq_iff (f g : SphericalSimplex Z z n) :
    f.homotopyClassStick = g.homotopyClassStick ↔
      f.val.HomotopicRel g.val (simplexBoundary n) := by
  change Quotient.mk' _ = Quotient.mk' _ ↔ _
  exact Quotient.eq.trans ⟨fun ⟨H⟩ ↦ ⟨homotopyFromGenLoopStick H⟩,
    fun ⟨H⟩ ↦ ⟨homotopyToGenLoopStick H⟩⟩

@[simp] theorem homotopyClassStick_const [Nonempty (Fin n)] :
    (const : SphericalSimplex Z z n).homotopyClassStick = 1 := rfl

/-- Nullhomotopy detection requires no unproved orientation comparison. -/
theorem homotopyClassStick_eq_one_iff [Nonempty (Fin n)] (f : SphericalSimplex Z z n) :
    f.homotopyClassStick = 1 ↔
      f.val.HomotopicRel (ContinuousMap.const _ z) (simplexBoundary n) := by
  rw [← homotopyClassStick_const (z := z), homotopyClassStick_eq_iff]
  rfl

/-- The explicit quotient and the chosen homeomorphism detect the same vanishing. -/
theorem homotopyClassStick_eq_one_iff_chosen [Nonempty (Fin n)] (f : SphericalSimplex Z z n) :
    f.homotopyClassStick = 1 ↔ f.homotopyClass = 1 := by
  cases n with
  | zero => exact Fin.elim0 (Classical.arbitrary (Fin 0))
  | succ n => rw [homotopyClassStick_eq_one_iff, homotopyClass_eq_one_iff]

end Quillen.SphericalSimplex
