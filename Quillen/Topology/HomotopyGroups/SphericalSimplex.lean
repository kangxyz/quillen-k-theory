/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Cube.SimplexPair

/-!
# Spherical singular simplices in the actual homotopy groups

The chosen cube/simplex pair homeomorphism identifies genuine singular simplices
constant on their entire boundary with the existing generalized loops. Both
maps act on actual relative homotopies. The resulting map to the existing
cubical homotopy group is surjective and detects precisely boundary-relative
homotopy. No alternative sphere homotopy group or orientation convention is
introduced here.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Convexity
open scoped Topology unitInterval

universe u

namespace Quillen

/-- A singular simplex sending its entire geometric boundary to the basepoint. -/
def SphericalSimplex (Z : Type u) [TopologicalSpace Z] (z : Z) (n : ℕ) :=
  {f : C(StdSimplex ℝ (Fin (n + 1)), Z) // ∀ x ∈ simplexBoundary n, f x = z}

namespace SphericalSimplex

variable {Z : Type u} [TopologicalSpace Z] {z : Z} {n : ℕ}

instance : FunLike (SphericalSimplex Z z n) (StdSimplex ℝ (Fin (n + 1))) Z where
  coe f := f.val
  coe_injective := fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h ↦ by congr

@[simp] theorem coe_val (f : SphericalSimplex Z z n) : ⇑f.val = f := rfl

@[ext] theorem ext {f g : SphericalSimplex Z z n} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.coe_injective (funext h)

@[simp] theorem boundary (f : SphericalSimplex Z z n)
    (x : StdSimplex ℝ (Fin (n + 1))) (hx : x ∈ simplexBoundary n) : f x = z :=
  f.property x hx

/-- The constant singular simplex. -/
def const : SphericalSimplex Z z n := ⟨ContinuousMap.const _ z, fun _ _ ↦ rfl⟩

@[simp] theorem const_apply (x : StdSimplex ℝ (Fin (n + 1))) :
    (const : SphericalSimplex Z z n) x = z := rfl

/-- Reparametrize the actual singular simplex by the chosen cube homeomorphism. -/
def toGenLoop (f : SphericalSimplex Z z n) : GenLoop (Fin n) Z z :=
  ⟨f.val.comp ⟨Cube.simplexHomeomorph n, (Cube.simplexHomeomorph n).continuous⟩, fun t ht ↦
    f.property _ ((Cube.simplexHomeomorph_mem_boundary_iff n t).mpr ht)⟩

@[simp] theorem toGenLoop_apply (f : SphericalSimplex Z z n) (t : Fin n → I) :
    f.toGenLoop t = f (Cube.simplexHomeomorph n t) := rfl

/-- Reparametrize an original generalized loop by the inverse pair homeomorphism. -/
def ofGenLoop (p : GenLoop (Fin n) Z z) : SphericalSimplex Z z n :=
  ⟨p.val.comp ⟨(Cube.simplexHomeomorph n).symm,
    (Cube.simplexHomeomorph n).symm.continuous⟩, fun x hx ↦ by
    apply p.property
    rw [← Cube.simplexHomeomorph_mem_boundary_iff]
    simpa using hx⟩

@[simp] theorem ofGenLoop_apply (p : GenLoop (Fin n) Z z)
    (x : StdSimplex ℝ (Fin (n + 1))) :
    ofGenLoop p x = p ((Cube.simplexHomeomorph n).symm x) := rfl

@[simp] theorem toGenLoop_ofGenLoop (p : GenLoop (Fin n) Z z) :
    (ofGenLoop p).toGenLoop = p := by
  ext t
  simp

@[simp] theorem ofGenLoop_toGenLoop (f : SphericalSimplex Z z n) :
    ofGenLoop f.toGenLoop = f := by
  ext x
  simp

/-- An equivalence on actual representatives, before taking any homotopy quotient. -/
def genLoopEquiv : SphericalSimplex Z z n ≃ GenLoop (Fin n) Z z where
  toFun := toGenLoop
  invFun := ofGenLoop
  left_inv := ofGenLoop_toGenLoop
  right_inv := toGenLoop_ofGenLoop

@[simp] theorem toGenLoop_const :
    (const : SphericalSimplex Z z n).toGenLoop = GenLoop.const := by
  ext t
  rfl

@[simp] theorem ofGenLoop_const :
    ofGenLoop (GenLoop.const : GenLoop (Fin n) Z z) = const := by
  ext x
  rfl

/-- An actual simplex-boundary-relative homotopy gives an actual cube-boundary-relative homotopy. -/
def homotopyToGenLoop {f g : SphericalSimplex Z z n}
    (H : f.val.HomotopyRel g.val (simplexBoundary n)) :
    f.toGenLoop.val.HomotopyRel g.toGenLoop.val (_root_.Cube.boundary (Fin n)) where
  toHomotopy := H.toHomotopy.compContinuousMap
    ⟨Cube.simplexHomeomorph n, (Cube.simplexHomeomorph n).continuous⟩
  prop' s t ht := H.eq_fst s ((Cube.simplexHomeomorph_mem_boundary_iff n t).mpr ht)

@[simp] theorem homotopyToGenLoop_apply {f g : SphericalSimplex Z z n}
    (H : f.val.HomotopyRel g.val (simplexBoundary n)) (s : I) (t : Fin n → I) :
    homotopyToGenLoop H (s, t) = H (s, Cube.simplexHomeomorph n t) := rfl

/-- Recover the whole simplex relative homotopy, retaining its original time parameter. -/
def homotopyFromGenLoop {f g : SphericalSimplex Z z n}
    (H : f.toGenLoop.val.HomotopyRel g.toGenLoop.val (_root_.Cube.boundary (Fin n))) :
    f.val.HomotopyRel g.val (simplexBoundary n) where
  toFun q := H (q.1, (Cube.simplexHomeomorph n).symm q.2)
  continuous_toFun := H.continuous.comp
    (continuous_fst.prodMk ((Cube.simplexHomeomorph n).symm.continuous.comp continuous_snd))
  map_zero_left x := by simp [H.apply_zero]
  map_one_left x := by simp [H.apply_one]
  prop' s x hx := by
    have ht : (Cube.simplexHomeomorph n).symm x ∈ _root_.Cube.boundary (Fin n) := by
      rw [← Cube.simplexHomeomorph_mem_boundary_iff]
      simpa using hx
    simpa using H.eq_fst s ht

@[simp] theorem homotopyFromGenLoop_apply {f g : SphericalSimplex Z z n}
    (H : f.toGenLoop.val.HomotopyRel g.toGenLoop.val (_root_.Cube.boundary (Fin n)))
    (s : I) (x : StdSimplex ℝ (Fin (n + 1))) :
    homotopyFromGenLoop H (s, x) = H (s, (Cube.simplexHomeomorph n).symm x) := rfl

/-- Reparametrization preserves and reflects genuine homotopy relative to the entire boundary. -/
theorem homotopic_iff (f g : SphericalSimplex Z z n) :
    GenLoop.Homotopic f.toGenLoop g.toGenLoop ↔
      f.val.HomotopicRel g.val (simplexBoundary n) :=
  ⟨fun ⟨H⟩ ↦ ⟨homotopyFromGenLoop H⟩, fun ⟨H⟩ ↦ ⟨homotopyToGenLoop H⟩⟩

/-- The class in the existing cubical homotopy set or group. -/
def homotopyClass (f : SphericalSimplex Z z n) : HomotopyGroup.Pi n Z z :=
  Quotient.mk' f.toGenLoop

@[simp] theorem homotopyClass_ofGenLoop (p : GenLoop (Fin n) Z z) :
    (ofGenLoop p).homotopyClass = Quotient.mk' p := by
  simp [homotopyClass]

/-- Every original homotopy class has an actual spherical singular-simplex representative. -/
theorem homotopyClass_surjective :
    Function.Surjective (homotopyClass : SphericalSimplex Z z n → HomotopyGroup.Pi n Z z) := by
  intro a
  refine Quotient.inductionOn a (fun p ↦ ?_)
  exact ⟨ofGenLoop p, homotopyClass_ofGenLoop p⟩

/-- Equality of original classes is exactly simplex-boundary-relative homotopy. -/
theorem homotopyClass_eq_iff (f g : SphericalSimplex Z z n) :
    f.homotopyClass = g.homotopyClass ↔ f.val.HomotopicRel g.val (simplexBoundary n) := by
  change Quotient.mk' f.toGenLoop = Quotient.mk' g.toGenLoop ↔ _
  exact Quotient.eq.trans (homotopic_iff f g)

/-- The class map respects a displayed relative homotopy, with no quotient model change. -/
theorem homotopyClass_eq_of_homotopy {f g : SphericalSimplex Z z n}
    (H : f.val.HomotopyRel g.val (simplexBoundary n)) : f.homotopyClass = g.homotopyClass :=
  (homotopyClass_eq_iff f g).mpr ⟨H⟩

@[simp] theorem homotopyClass_const (n : ℕ) :
    (const : SphericalSimplex Z z (n + 1)).homotopyClass = 1 := by
  simp only [homotopyClass, toGenLoop_const, HomotopyGroup.one_def]
  rfl

/-- The unit criterion is a genuine boundary-fixed nullhomotopy of the singular simplex. -/
theorem homotopyClass_eq_one_iff (f : SphericalSimplex Z z (n + 1)) :
    f.homotopyClass = 1 ↔
      f.val.HomotopicRel (ContinuousMap.const _ z) (simplexBoundary (n + 1)) := by
  rw [← homotopyClass_const (z := z) n, homotopyClass_eq_iff]
  rfl

/-- Additive notation for the same actual group in the range where it is commutative. -/
def additiveClass (f : SphericalSimplex Z z (n + 2)) :
    Additive (HomotopyGroup.Pi (n + 2) Z z) := Additive.ofMul f.homotopyClass

@[simp] theorem additiveClass_const (n : ℕ) :
    (const : SphericalSimplex Z z (n + 2)).additiveClass = 0 := by
  change (const : SphericalSimplex Z z (n + 2)).homotopyClass = 1
  exact homotopyClass_const (n + 1)

/-- The additive wrapper has the original commutative-group structure, not new operations. -/
theorem additiveClass_surjective (n : ℕ) : Function.Surjective
    (additiveClass : SphericalSimplex Z z (n + 2) → Additive (HomotopyGroup.Pi (n + 2) Z z)) :=
  homotopyClass_surjective

end SphericalSimplex
end Quillen
