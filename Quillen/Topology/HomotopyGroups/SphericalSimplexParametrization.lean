/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.SphericalSimplex

/-!
# Spherical-simplex representation with a specified pair homeomorphism

An explicit pair homeomorphism may be retained as data throughout the
representation theorem. This allows a future signed addition construction to
supply a geometrically controlled parametrization without comparing it to
an unrelated existential choice. No orientation property follows from the
boundary condition alone, and no such property is asserted here.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Convexity
open scoped Topology unitInterval
universe u

namespace Quillen.SphericalSimplex
variable {Z : Type u} [TopologicalSpace Z] {z : Z} {n : ℕ}

/-- Reparametrization by the specified boundary-pair homeomorphism. -/
def toGenLoopWith (f : SphericalSimplex Z z n)
    (e : (Fin n → I) ≃ₜ StdSimplex ℝ (Fin (n + 1)))
    (he : ∀ t, e t ∈ simplexBoundary n ↔ t ∈ _root_.Cube.boundary (Fin n)) :
    GenLoop (Fin n) Z z :=
  ⟨f.val.comp ⟨e, e.continuous⟩, fun t ht ↦ f.property _ ((he t).mpr ht)⟩

/-- Inverse reparametrization by the same specified pair homeomorphism. -/
def ofGenLoopWith (p : GenLoop (Fin n) Z z)
    (e : (Fin n → I) ≃ₜ StdSimplex ℝ (Fin (n + 1)))
    (he : ∀ t, e t ∈ simplexBoundary n ↔ t ∈ _root_.Cube.boundary (Fin n)) :
    SphericalSimplex Z z n :=
  ⟨p.val.comp ⟨e.symm, e.symm.continuous⟩, fun x hx ↦ by
    apply p.property
    rw [← he]
    simpa using hx⟩

variable (e : (Fin n → I) ≃ₜ StdSimplex ℝ (Fin (n + 1)))
  (he : ∀ t, e t ∈ simplexBoundary n ↔ t ∈ _root_.Cube.boundary (Fin n))

@[simp] theorem toGenLoopWith_apply (f : SphericalSimplex Z z n) (t : Fin n → I) :
    f.toGenLoopWith e he t = f (e t) := rfl

@[simp] theorem ofGenLoopWith_apply (p : GenLoop (Fin n) Z z)
    (x : StdSimplex ℝ (Fin (n + 1))) : ofGenLoopWith p e he x = p (e.symm x) := rfl

@[simp] theorem toGenLoopWith_ofGenLoopWith (p : GenLoop (Fin n) Z z) :
    (ofGenLoopWith p e he).toGenLoopWith e he = p := by ext t; simp

@[simp] theorem ofGenLoopWith_toGenLoopWith (f : SphericalSimplex Z z n) :
    ofGenLoopWith (f.toGenLoopWith e he) e he = f := by ext x; simp

/-- The representative equivalence retains the specified geometric homeomorphism. -/
def genLoopEquivWith : SphericalSimplex Z z n ≃ GenLoop (Fin n) Z z where
  toFun f := f.toGenLoopWith e he
  invFun p := ofGenLoopWith p e he
  left_inv := ofGenLoopWith_toGenLoopWith e he
  right_inv := toGenLoopWith_ofGenLoopWith e he

/-- Transport a displayed relative homotopy using the specified homeomorphism. -/
def homotopyToGenLoopWith {f g : SphericalSimplex Z z n}
    (H : f.val.HomotopyRel g.val (simplexBoundary n)) :
    (f.toGenLoopWith e he).val.HomotopyRel (g.toGenLoopWith e he).val
      (_root_.Cube.boundary (Fin n)) where
  toHomotopy := H.toHomotopy.compContinuousMap ⟨e, e.continuous⟩
  prop' s t ht := H.eq_fst s ((he t).mpr ht)

/-- Recover the full relative homotopy using the inverse specified homeomorphism. -/
def homotopyFromGenLoopWith {f g : SphericalSimplex Z z n}
    (H : (f.toGenLoopWith e he).val.HomotopyRel (g.toGenLoopWith e he).val
      (_root_.Cube.boundary (Fin n))) : f.val.HomotopyRel g.val (simplexBoundary n) where
  toFun q := H (q.1, e.symm q.2)
  continuous_toFun := H.continuous.comp
    (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd))
  map_zero_left x := by simp [H.apply_zero]
  map_one_left x := by simp [H.apply_one]
  prop' s x hx := by
    have ht : e.symm x ∈ _root_.Cube.boundary (Fin n) := by
      rw [← he]
      simpa using hx
    simpa using H.eq_fst s ht

/-- The class associated with a specified pair homeomorphism belongs to the original Pi n. -/
def homotopyClassWith (f : SphericalSimplex Z z n) : HomotopyGroup.Pi n Z z :=
  Quotient.mk' (f.toGenLoopWith e he)

/-- Every original class has a representative for any specified pair homeomorphism. -/
theorem homotopyClassWith_surjective : Function.Surjective
    (homotopyClassWith e he : SphericalSimplex Z z n → HomotopyGroup.Pi n Z z) := by
  intro a
  refine Quotient.inductionOn a (fun p ↦ ?_)
  refine ⟨ofGenLoopWith p e he, ?_⟩
  simp only [homotopyClassWith, toGenLoopWith_ofGenLoopWith]
  rfl

/-- Equality of original classes still detects exactly genuine relative homotopy. -/
theorem homotopyClassWith_eq_iff (f g : SphericalSimplex Z z n) :
    homotopyClassWith e he f = homotopyClassWith e he g ↔
      f.val.HomotopicRel g.val (simplexBoundary n) := by
  change Quotient.mk' _ = Quotient.mk' _ ↔ _
  exact Quotient.eq.trans ⟨fun ⟨H⟩ ↦ ⟨homotopyFromGenLoopWith e he H⟩,
    fun ⟨H⟩ ↦ ⟨homotopyToGenLoopWith e he H⟩⟩

/-- Constants represent the existing unit for every specified parametrization. -/
@[simp] theorem homotopyClassWith_const [Nonempty (Fin n)] :
    homotopyClassWith e he (const : SphericalSimplex Z z n) = 1 := by
  rfl

/-- Unit detection depends only on an actual simplex nullhomotopy, for any parametrization. -/
theorem homotopyClassWith_eq_one_iff [Nonempty (Fin n)] (f : SphericalSimplex Z z n) :
    homotopyClassWith e he f = 1 ↔
      f.val.HomotopicRel (ContinuousMap.const _ z) (simplexBoundary n) := by
  rw [← homotopyClassWith_const (z := z) e he, homotopyClassWith_eq_iff]
  rfl

/-- All specified pair parametrizations detect the same vanishing, without an orientation claim. -/
theorem homotopyClassWith_eq_one_iff_of_parametrization [Nonempty (Fin n)]
    (e' : (Fin n → I) ≃ₜ StdSimplex ℝ (Fin (n + 1)))
    (he' : ∀ t, e' t ∈ simplexBoundary n ↔ t ∈ _root_.Cube.boundary (Fin n))
    (f : SphericalSimplex Z z n) :
    homotopyClassWith e he f = 1 ↔ homotopyClassWith e' he' f = 1 := by
  rw [homotopyClassWith_eq_one_iff, homotopyClassWith_eq_one_iff]

/-- The original chosen-homeomorphism API is precisely this specialization. -/
theorem homotopyClassWith_chosen (f : SphericalSimplex Z z n) :
    homotopyClassWith (Cube.simplexHomeomorph n) (Cube.simplexHomeomorph_mem_boundary_iff n) f =
      f.homotopyClass := rfl

end Quillen.SphericalSimplex
