/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.TheoremA.RealizationBoundary
public import Mathlib.Topology.Piecewise

/-! # Both interval endpoints have the homotopy extension property -/
@[expose] public section


noncomputable section

open CategoryTheory MonoidalCategory Convexity
open scoped Topology unitInterval

universe u

namespace Quillen.TheoremA

attribute [local instance] Classical.propDecidable

/-- The two vertices are all points of the geometric one-simplex boundary. -/
theorem simplexBoundary_one_cases (b : simplexBoundary 1) :
    b.1 = StdSimplex.single 0 ∨ b.1 = StdSimplex.single 1 := by
  have hs : b.1.weights 0 + b.1.weights 1 = 1 := by
    simp
  obtain ⟨i, hi⟩ := b.2
  fin_cases i
  · right
    change b.1.weights 0 = 0 at hi
    have h1 : b.1.weights 1 = 1 := by linarith
    apply StdSimplex.ext
    ext j
    fin_cases j <;> simp [hi, h1]
  · left
    change b.1.weights 1 = 0 at hi
    have h0 : b.1.weights 0 = 1 := by linarith
    apply StdSimplex.ext
    ext j
    fin_cases j <;> simp [hi, h0]

/-- The first interval endpoint as a simplex-boundary point. -/
def boundaryZero : simplexBoundary 1 :=
  ⟨StdSimplex.single 0, ⟨1, by simp⟩⟩

/-- The second interval endpoint as a simplex-boundary point. -/
def boundaryOne : simplexBoundary 1 :=
  ⟨StdSimplex.single 1, ⟨0, by simp⟩⟩

lemma boundaryZero_ne_one : boundaryZero ≠ boundaryOne := by
  intro h
  have h' := congrArg (fun b : simplexBoundary 1 ↦ StdSimplex.homeomorphI b.1) h
  simp [boundaryZero, boundaryOne] at h'

lemma boundary_eq_zero_or_one (b : simplexBoundary 1) : b = boundaryZero ∨ b = boundaryOne := by
  rcases simplexBoundary_one_cases b with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

local instance : Finite (simplexBoundary 1) := by
  apply Finite.of_surjective (fun b : Bool ↦ if b then boundaryOne else boundaryZero)
  intro b
  rcases boundary_eq_zero_or_one b with rfl | rfl
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

/-- The disjoint union of two copies of a space is its product with the simplex boundary. -/
def intervalEndpointDomainHomeomorph (A : Type u) [TopologicalSpace A] :
    (A ⊕ A) ≃ₜ A × simplexBoundary 1 where
  toFun := Sum.elim (fun a ↦ (a, boundaryZero)) (fun a ↦ (a, boundaryOne))
  invFun z := if z.2 = boundaryZero then Sum.inl z.1 else Sum.inr z.1
  left_inv a := by
    cases a <;> simp [boundaryZero_ne_one.symm]
  right_inv z := by
    rcases z with ⟨a, b⟩
    rcases boundary_eq_zero_or_one b with rfl | rfl <;>
      simp [boundaryZero_ne_one.symm]
  continuous_toFun := continuous_sum_dom.mpr ⟨by fun_prop, by fun_prop⟩
  continuous_invFun := by
    apply continuous_if
    · intro z hz
      have hc : IsClopen {z : A × simplexBoundary 1 | z.2 = boundaryZero} :=
        (isClopen_discrete {boundaryZero}).preimage continuous_snd
      rw [hc.frontier_eq] at hz
      exact False.elim hz
    · exact (continuous_inl.comp continuous_fst).continuousOn
    · exact (continuous_inr.comp continuous_fst).continuousOn

/-- The usual inclusion of both endpoints in a topological cylinder. -/
def intervalEndpoints (A : TopCat.{u}) : TopCat.of (A ⊕ A) ⟶ A ⊗ TopCat.I :=
  TopCat.ofHom ⟨Sum.elim (fun a ↦ (a, ULift.up 0)) (fun a ↦ (a, ULift.up 1)),
    continuous_sum_dom.mpr ⟨by fun_prop, by fun_prop⟩⟩

/-- The endpoint pair inclusion has HEP after product with any space. -/
theorem homotopyExtensionProperty_intervalEndpoints (A : TopCat.{u}) :
    homotopyExtensionProperty (intervalEndpoints A) := by
  let e₁ : TopCat.of (A ⊕ A) ≅ TopCat.of (A × simplexBoundary 1) :=
    TopCat.isoOfHomeo (intervalEndpointDomainHomeomorph A)
  let e₂ : TopCat.of (A × StdSimplex ℝ (Fin 2)) ≅ A ⊗ TopCat.I :=
    TopCat.isoOfHomeo ((Homeomorph.refl A).prodCongr
      (StdSimplex.homeomorphI.trans TopCat.I.homeomorph.symm))
  have h := homotopyExtensionProperty_comp
    (homotopyExtensionProperty_comp
      (homotopyExtensionProperty_of_isIso e₁.hom)
      (homotopyExtensionProperty_simplexBoundary A 1))
    (homotopyExtensionProperty_of_isIso e₂.hom)
  have heq : (e₁.hom ≫ parameterizedSimplexBoundaryInclusion A 1) ≫ e₂.hom =
      intervalEndpoints A := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    cases a with
    | inl a =>
      change (a, ULift.up (StdSimplex.homeomorphI (StdSimplex.single 0))) = (a, ULift.up 0)
      rw [StdSimplex.homeomorphI_single_zero]
    | inr a =>
      change (a, ULift.up (StdSimplex.homeomorphI (StdSimplex.single 1))) = (a, ULift.up 1)
      rw [StdSimplex.homeomorphI_single_one]
  exact heq ▸ h

end Quillen.TheoremA
