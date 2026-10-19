/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputWeakZeroProduct

/-! Regression checks for the selected weak localization null and exact finite products. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.PerfectComplexes
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.GlobalBassWeakZeroRecipe
open GlobalBassEvaluation GlobalSectionChangeIndex ParameterAuxiliarySupport
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)
  (X : Scheme.{u}ᵒᵖ) {k : ℕ}
  (N : Fin (k + 1) → CommonReferenceNerve.Node (InputWeakZero.reference f T X))

/-- Every value is the unchanged selected-zero path at the original reversed time. -/
theorem selected_null (n : ℕ) (r : I) (x : (prespectrum ((fiber f T).obj X)).space n) :
    prespectrumSimplexFamily (InputWeakZero.simplex f T X N) n
      ((edge (k := k + 2) 0 1).symm r, x) =
        (prespectrumTransformationHomotopy (zeroToFull f T X)
          (zeroToFull_weak f T X)).level n (unitInterval.symm r, x) :=
  (InputWeakZero.null_native f T X N n r x).trans (fullNull_level f T X n r x)

/-- The whole normalization simplex retains every full dependent reference node. -/
theorem whole_normalization (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (prespectrum ((fiber f T).obj X)).space n) :
    prespectrumSimplexFamily (InputWeakZero.simplex f T X N) n
      (StdSimplex.map Fin.succ (StdSimplex.map Fin.succ z), x) =
        CommonReferenceNerve.prespectrumFamily (InputWeakZero.reference f T X) N n (z, x) :=
  InputWeakZero.normalization_native f T X N n z x

/-- Prespectrum level zero retains a separate old input-loop coordinate. -/
theorem level_zero (r t : I) (x : (prespectrum ((fiber f T).obj X)).space 0) :
    Path.toContinuousMap (InputWeakZero.family f T X N 0 ((r, StdSimplex.single 0), x)) t =
      Path.toContinuousMap (((fullNull f T).homotopy X).level 0 (r, x)) t :=
  congrArg (fun p ↦ Path.toContinuousMap p t) (InputWeakZero.family_null f T X N 0 r x)

/-- Every normalization parameter terminates at the same original native zero. -/
theorem terminal_zero (n : ℕ) (z : StdSimplex ℝ (Fin (k + 2)))
    (x : (prespectrum ((fiber f T).obj X)).space n) :
    InputWeakZero.family f T X N n ((1, z), x) =
      (prespectrum ((openModel f T).obj X)).point n :=
  CommonReferenceWeakZero.coneFamily_one (InputWeakZero.reference f T X) N
    (zeroToFull f T X) (zeroToFull_weak f T X) n z x

/-- Original structure time remains independent of both finite-family coordinates. -/
theorem structure_time (n : ℕ) (r t : I) (z : StdSimplex ℝ (Fin (k + 2)))
    (x : (prespectrum ((fiber f T).obj X)).space n) :
    InputWeakZero.family f T X N (n + 1)
        ((r, z), (prespectrum ((fiber f T).obj X)).structureMap n x t) =
      (prespectrum ((openModel f T).obj X)).structureMap n
        (InputWeakZero.family f T X N n ((r, z), x)) t :=
  InputWeakZero.family_structure f T X N n r z x t

/-- Arbitrary coefficient change preserves every original null-slice time. -/
theorem coefficient_slice {Y : Scheme.{u}ᵒᵖ} (a : X ⟶ Y) {l : ℕ}
    (M : Fin (l + 1) → CommonReferenceNerve.Node (InputWeakZero.reference f T Y))
    (n : ℕ) (r : I) (x : (prespectrum ((fiber f T).obj X)).space n) :
    (prespectrumMap ((openModel f T).map a)).map n
        (InputWeakZero.family f T X N n ((r, StdSimplex.single 0), x)) =
      InputWeakZero.family f T Y M n ((r, StdSimplex.single 0),
        (prespectrumMap ((fiber f T).map a)).map n x) :=
  InputWeakZero.null_slice_naturality f T X N a M n r x

/-- The canonical null and original Laurent action retain two independent times. -/
theorem laurent_interchange {l : ℕ}
    (M : Fin (l + 1) → CommonReferenceNerve.Node
      (InputWeakZero.reference f T
        (AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.laurent.op.obj X)))
    (n : ℕ) (r s : I) (x : (prespectrum ((fiber f T).obj X)).space n) :
    InputWeakZero.family f T
        (AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.laurent.op.obj X) M n
        ((r, StdSimplex.single 0),
          ((ParameterLaurentTrack.supportedTrack (unionOpen f T).ι).homotopy X).level n (s, x)) =
      ((ParameterLaurentTrack.supportedTrack (inverseOpen f T).ι).homotopy X).level n
        (s, InputWeakZero.family f T X N n ((r, StdSimplex.single 0), x)) :=
  InputWeakZero.null_slice_laurentInterchange f T X N M n r s x

variable {l : ℕ} {R : Model.{u + 1}} (G₀ : (openModel f T).obj X ⟶ R)
  (G : Fin (l + 1) → ((openModel f T).obj X ⟶ R))
  (anchors : ∀ i, G₀.functor ≅ (G i).functor)

/-- The literal product interior recovers the original null followed by whole normalization. -/
theorem product_interior (n : ℕ) (r : I) (z : StdSimplex ℝ (Fin (l + 1)))
    (x : (prespectrum ((fiber f T).obj X)).space n) :
    prespectrumSimplexFamily (InputWeakZeroProduct.simplex f T X N G₀ G anchors) n
      (InputWeakZeroProduct.parameter.{u} (r, z), x) =
      prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G anchors) n
        (z, (prespectrumTransformationHomotopy (zeroToFull f T X)
          (zeroToFull_weak f T X)).level n (unitInterval.symm r, x)) := by
  rw [InputWeakZeroProduct.native, fullNull_level]

/-- The true two-factor product retains the independent original structure time. -/
theorem product_structure (n : ℕ) (r t : I) (z : StdSimplex ℝ (Fin (l + 1)))
    (x : (prespectrum ((fiber f T).obj X)).space n) :
    InputWeakZeroProduct.family f T X N G₀ G anchors (n + 1)
        ((r, z), (prespectrum ((fiber f T).obj X)).structureMap n x t) =
      (prespectrum R).structureMap n
        (InputWeakZeroProduct.family f T X N G₀ G anchors n ((r, z), x)) t :=
  InputWeakZeroProduct.family_structure f T X N G₀ G anchors n r z x t

end QuillenTest.GlobalBassWeakZeroRecipe
