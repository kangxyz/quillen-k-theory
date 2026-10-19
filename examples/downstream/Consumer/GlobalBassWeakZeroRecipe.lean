/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputWeakZeroProduct

/-! Independent consumers of the actual selected localization null, without a zero isomorphism. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open scoped Topology unitInterval
universe u
namespace Consumer.GlobalBassWeakZeroRecipe
open GlobalBassEvaluation GlobalSectionChangeIndex ParameterAuxiliarySupport
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)
  (X : Scheme.{u}ᵒᵖ) {k : ℕ}
  (N : Fin (k + 1) → CommonReferenceNerve.Node (InputWeakZero.reference f T X))

/-- The finite attachment keeps the exact canonical null at every time. -/
theorem prescribed_null (n : ℕ) (r : I) (x : (prespectrum ((fiber f T).obj X)).space n) :
    InputWeakZero.family f T X N n ((r, StdSimplex.single 0), x) =
      ((fullNull f T).homotopy X).level n (r, x) :=
  InputWeakZero.family_null f T X N n r x

/-- At prespectrum level zero the old loop time stays separate from the null time. -/
theorem old_loop_time (r t : I) (x : (prespectrum ((fiber f T).obj X)).space 0) :
    Path.toContinuousMap (InputWeakZero.family f T X N 0 ((r, StdSimplex.single 0), x)) t =
      Path.toContinuousMap (((fullNull f T).homotopy X).level 0 (r, x)) t :=
  congrArg (fun p ↦ Path.toContinuousMap p t) (prescribed_null f T X N 0 r x)

/-- All-dimensional target normalization is the actual independently parameterized product. -/
theorem normalization_product {l : ℕ} {R : Model.{u + 1}}
    (G₀ : (openModel f T).obj X ⟶ R)
    (G : Fin (l + 1) → ((openModel f T).obj X ⟶ R))
    (anchors : ∀ i, G₀.functor ≅ (G i).functor)
    (n : ℕ) (r : I) (z : StdSimplex ℝ (Fin (l + 1)))
    (x : (prespectrum ((fiber f T).obj X)).space n) :
    prespectrumSimplexFamily (InputWeakZeroProduct.simplex f T X N G₀ G anchors) n
      (InputWeakZeroProduct.parameter.{u} (r, z), x) =
      prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G anchors) n
        (z, ((fullNull f T).homotopy X).level n (r, x)) :=
  InputWeakZeroProduct.native f T X N G₀ G anchors n r z x

end Consumer.GlobalBassWeakZeroRecipe
