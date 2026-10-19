/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Topology.Path

/-!
# Fixed-endpoint path families and relative boundary extension

Intended upstream module: `Aglib.Topology.Path.FamilyExtension`.
For a closed subset `S` of an arbitrary space `B`, a continuous family of paths with fixed,
possibly different endpoints gives a continuous map on `(S × I) ∪ (B × {0, 1})`.
An actual extension of this map to `B × I` gives an extension of the original path family.
There are no compactness, separation, or chosen-point HEP hypotheses. Both endpoints and the
entire side family, including its original path coordinate, are recovered exactly.

The current consumer is `Quillen.Topology.HELP.PathCubeExtension`, which transports the literal
finite-cube boundary to this product boundary and uses one higher-dimensional scalar extension.
-/

@[expose] public noncomputable section

open scoped Topology unitInterval

universe u v

namespace Path

variable {B : Type u} {X : Type v} [TopologicalSpace B] [TopologicalSpace X]
  {a b : X}

/-- The original side together with both endpoint caps, with no quotient of the path time. -/
abbrev FamilyBoundary (S : Set B) :=
  {z : B × I // z.1 ∈ S ∨ z.2 = 0 ∨ z.2 = 1}

/-- Set-level side/cap pasting for a fixed-endpoint path family. -/
def familyBoundaryFun {S : Set B} (p : C(S, Path a b)) (z : FamilyBoundary S) : X := by
  classical
  exact if hz : z.val.1 ∈ S then p ⟨z.val.1, hz⟩ z.val.2 else if z.val.2 = 0 then a else b

@[simp] theorem familyBoundaryFun_side {S : Set B} (p : C(S, Path a b))
    (z : S) (t : I) :
    familyBoundaryFun p ⟨(z.val, t), Or.inl z.property⟩ = p z t := by
  simp [familyBoundaryFun, z.property]

@[simp] theorem familyBoundaryFun_zero {S : Set B} (p : C(S, Path a b)) (z : B) :
    familyBoundaryFun p ⟨(z, 0), Or.inr (Or.inl rfl)⟩ = a := by
  classical
  by_cases hz : z ∈ S <;> simp [familyBoundaryFun, hz]

@[simp] theorem familyBoundaryFun_one {S : Set B} (p : C(S, Path a b)) (z : B) :
    familyBoundaryFun p ⟨(z, 1), Or.inr (Or.inr rfl)⟩ = b := by
  classical
  by_cases hz : z ∈ S <;> simp [familyBoundaryFun, hz]

/-- Closed-set pasting preserves the supplied side and the two separate endpoint caps. -/
theorem continuous_familyBoundaryFun {S : Set B} (hS : IsClosed S)
    (p : C(S, Path a b)) : Continuous (familyBoundaryFun p) := by
  let A : Set (FamilyBoundary S) := {z | z.val.1 ∈ S}
  let D : Set (FamilyBoundary S) := {z | z.val.2 = 0}
  let E : Set (FamilyBoundary S) := {z | z.val.2 = 1}
  have hA : IsClosed A := hS.preimage (by fun_prop)
  have hD : IsClosed D := isClosed_eq (by fun_prop) continuous_const
  have hE : IsClosed E := isClosed_eq (by fun_prop) continuous_const
  have hcover : A ∪ (D ∪ E) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    exact z.property
  rw [← continuousOn_univ, ← hcover]
  apply ContinuousOn.union_of_isClosed _ _ hA (hD.union hE)
  · rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun z : A ↦ p ⟨z.val.val.1, z.property⟩ z.val.val.2) := by
      fun_prop
    convert hc using 1
    funext z
    exact familyBoundaryFun_side p ⟨z.val.val.1, z.property⟩ z.val.val.2
  · apply ContinuousOn.union_of_isClosed _ _ hD hE
    · rw [continuousOn_iff_continuous_domRestrict]
      convert (continuous_const : Continuous (fun _ : D ↦ a)) using 1
      funext z
      have hz : z.val.val.2 = 0 := z.property
      have he : z.val = (⟨(z.val.val.1, 0), Or.inr (Or.inl rfl)⟩ : FamilyBoundary S) :=
        Subtype.ext (Prod.ext rfl hz)
      exact (congrArg (familyBoundaryFun p) he).trans (familyBoundaryFun_zero p z.val.val.1)
    · rw [continuousOn_iff_continuous_domRestrict]
      convert (continuous_const : Continuous (fun _ : E ↦ b)) using 1
      funext z
      have hz : z.val.val.2 = 1 := z.property
      have he : z.val = (⟨(z.val.val.1, 1), Or.inr (Or.inr rfl)⟩ : FamilyBoundary S) :=
        Subtype.ext (Prod.ext rfl hz)
      exact (congrArg (familyBoundaryFun p) he).trans (familyBoundaryFun_one p z.val.val.1)

/-- The continuous relative-boundary map with the original path family on its entire side. -/
def familyBoundaryMap {S : Set B} (hS : IsClosed S) (p : C(S, Path a b)) :
    C(FamilyBoundary S, X) :=
  ⟨familyBoundaryFun p, continuous_familyBoundaryFun hS p⟩

@[simp] theorem familyBoundaryMap_side {S : Set B} (hS : IsClosed S)
    (p : C(S, Path a b)) (z : S) (t : I) :
    familyBoundaryMap hS p ⟨(z.val, t), Or.inl z.property⟩ = p z t :=
  familyBoundaryFun_side p z t

@[simp] theorem familyBoundaryMap_zero {S : Set B} (hS : IsClosed S)
    (p : C(S, Path a b)) (z : B) :
    familyBoundaryMap hS p ⟨(z, 0), Or.inr (Or.inl rfl)⟩ = a :=
  familyBoundaryFun_zero p z

@[simp] theorem familyBoundaryMap_one {S : Set B} (hS : IsClosed S)
    (p : C(S, Path a b)) (z : B) :
    familyBoundaryMap hS p ⟨(z, 1), Or.inr (Or.inr rfl)⟩ = b :=
  familyBoundaryFun_one p z

/-- Curry one supplied scalar extension; the path coordinate is unchanged. -/
def familyExtension {S : Set B} (hS : IsClosed S) (p : C(S, Path a b))
    (F : C(B × I, X)) (hF : ∀ z : FamilyBoundary S, F z.val = familyBoundaryMap hS p z) :
    C(B, Path a b) where
  toFun z :=
    { toFun t := F (z, t)
      continuous_toFun := by fun_prop
      source' := (hF ⟨(z, 0), Or.inr (Or.inl rfl)⟩).trans (familyBoundaryMap_zero hS p z)
      target' := (hF ⟨(z, 1), Or.inr (Or.inr rfl)⟩).trans (familyBoundaryMap_one hS p z) }
  continuous_toFun := Path.continuous_uncurry_iff.mp F.continuous

@[simp] theorem familyExtension_apply {S : Set B} (hS : IsClosed S)
    (p : C(S, Path a b)) (F : C(B × I, X))
    (hF : ∀ z : FamilyBoundary S, F z.val = familyBoundaryMap hS p z) (z : B) (t : I) :
    familyExtension hS p F hF z t = F (z, t) := rfl

/-- Every specified side path is recovered as a path, not only at its endpoints. -/
@[simp] theorem familyExtension_side {S : Set B} (hS : IsClosed S)
    (p : C(S, Path a b)) (F : C(B × I, X))
    (hF : ∀ z : FamilyBoundary S, F z.val = familyBoundaryMap hS p z) (z : S) :
    familyExtension hS p F hF z.val = p z := by
  ext t
  exact (hF ⟨(z.val, t), Or.inl z.property⟩).trans (familyBoundaryMap_side hS p z t)

/-- A scalar extension property on the relative cylinder boundary extends every fixed-endpoint
path family on the original closed subset. The endpoints are allowed to be different. -/
theorem exists_family_extension {S : Set B} (hS : IsClosed S)
    (extend : ∀ f : C(FamilyBoundary S, X),
      ∃ F : C(B × I, X), ∀ z : FamilyBoundary S, F z.val = f z)
    (p : C(S, Path a b)) : ∃ P : C(B, Path a b), ∀ z : S, P z.val = p z := by
  obtain ⟨F, hF⟩ := extend (familyBoundaryMap hS p)
  exact ⟨familyExtension hS p F hF, familyExtension_side hS p F hF⟩

end Path
