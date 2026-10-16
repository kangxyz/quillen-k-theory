/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarCofiberInputDescent

/-! # Exact scalar input representatives and conditional class descent -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.Additivity
open scoped Simplicial Topology
universe u v
namespace QuillenTest.ScalarCofiberInputDescent
variable (X : Scheme.{u})

/-- Every original K-class is represented by the unchanged scalar projection input. -/
theorem original_input_coverage (n : ℕ) (a : (perfectWaldhausen X).K n) :
    ∃ p : GenLoop (Fin (n + 1))
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
      (subdivisionBasepoint (perfectWaldhausen X)),
      (⟦perfectScalarProjectionInputCube n p⟧ : (perfectWaldhausen X).K n) = a :=
  perfectScalarProjectionInputCube_class_surjective X n a

/-- The same representative coverage includes degree zero without an input vanishing hypothesis. -/
theorem original_input_degree_zero (a : (perfectWaldhausen X).K 0) :
    ∃ p : GenLoop (Fin 1)
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
      (subdivisionBasepoint (perfectWaldhausen X)),
      (⟦perfectScalarProjectionInputCube 0 p⟧ : (perfectWaldhausen X).K 0) = a :=
  perfectScalarProjectionInputCube_class_surjective X 0 a

/-- The all-class property still requires its complete original representative-level proof. -/
theorem original_property_descent (n : ℕ) (P : (perfectWaldhausen X).K n → Prop)
    (h : ∀ p : GenLoop (Fin (n + 1))
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
      (subdivisionBasepoint (perfectWaldhausen X)), P ⟦perfectScalarProjectionInputCube n p⟧) :
    ∀ a, P a :=
  perfectScalarProjectionInputCube_forall X n P h

/-- A comparison of original homomorphisms descends from the supplied literal-input equation. -/
theorem original_homomorphism_descent (n : ℕ) {G : Type v} [Monoid G]
    (f g : (perfectWaldhausen X).K n →* G)
    (h : ∀ p : GenLoop (Fin (n + 1))
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
      (subdivisionBasepoint (perfectWaldhausen X)),
      f ⟦perfectScalarProjectionInputCube n p⟧ = g ⟦perfectScalarProjectionInputCube n p⟧) :
    f = g :=
  perfectScalarProjectionInputCube_hom_ext X n f g h

end QuillenTest.ScalarCofiberInputDescent
