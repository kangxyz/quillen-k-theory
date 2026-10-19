/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputWeakZero
public import Quillen.Waldhausen.SConstruction.Iterated.RealizationMixedWeakProduct

/-!
# The original localization null followed by a whole normalization family

The weak factor is the original supported null, with its unchanged reversed time. The second
factor is an actual isomorphism-reference family. The product uses the selected realization-grid
parameter, not the affine normalization cone. No precomposition or weak-by-weak product is claimed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputWeakZeroProduct
open GlobalSectionChangeIndex GlobalSectionChangeIndex.ParameterAuxiliarySupport
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)
  (X : Scheme.{u}ᵒᵖ) {k l : ℕ}
  (N : Fin (k + 1) → CommonReferenceNerve.Node (InputWeakZero.reference f T X))
  {R : Model.{u + 1}} (G₀ : (openModel f T).obj X ⟶ R)
  (G : Fin (l + 1) → ((openModel f T).obj X ⟶ R))
  (anchors : ∀ i, G₀.functor ≅ (G i).functor)

/-- The weak major coordinate is never inverted; the target chain uses its actual anchors. -/
def simplex := MixedWeakProduct.simplex (InputWeakZero.simplex f T X N) G₀ G anchors

/-- The two independent parameters retain the actual realization-product inverse. -/
def parameter : C(unitInterval × StdSimplex ℝ (Fin (l + 1)),
    StdSimplex ℝ (Fin (Quillen.SimplexGrid.dimension (k + 2) l + 1))) :=
  (Quillen.SimplexGrid.parameter.{u+1} (k + 2) l).comp
    ⟨fun z ↦ ((edge (k := k + 2) 0 1).symm z.1, z.2), by fun_prop⟩

/-- Every value is the original whole target family after the same canonical null. -/
theorem native (n : ℕ) (r : unitInterval) (z : StdSimplex ℝ (Fin (l + 1)))
    (x : (prespectrum ((fiber f T).obj X)).space n) :
    prespectrumSimplexFamily (simplex f T X N G₀ G anchors) n (parameter.{u} (r, z), x) =
      prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G anchors) n
        (z, ((fullNull f T).homotopy X).level n (r, x)) := by
  change prespectrumSimplexFamily
    (MixedWeakProduct.simplex (InputWeakZero.simplex f T X N) G₀ G anchors) n
    (Quillen.SimplexGrid.parameter.{u+1} (k + 2) l
      ((edge (k := k + 2) 0 1).symm r, z), x) = _
  rw [MixedWeakProduct.prespectrum_comp, InputWeakZero.null_native]

/-- The native product is continuous in both original parameter factors. -/
def family (n : ℕ) : C((unitInterval × StdSimplex ℝ (Fin (l + 1))) ×
    (prespectrum ((fiber f T).obj X)).space n, (prespectrum R).space n) :=
  (prespectrumSimplexFamily (simplex f T X N G₀ G anchors) n).comp
    ⟨fun z ↦ (parameter.{u} z.1, z.2), by fun_prop⟩

/-- Every product parameter fixes the actual native basepoint. -/
theorem point (n : ℕ) (r : unitInterval) (z : StdSimplex ℝ (Fin (l + 1))) :
    family f T X N G₀ G anchors n ((r, z), (prespectrum ((fiber f T).obj X)).point n) =
      (prespectrum R).point n := prespectrumSimplexFamily_point _ _ _

/-- Neither null nor normalization time is identified with the original structure coordinate. -/
theorem family_structure (n : ℕ) (r : unitInterval) (z : StdSimplex ℝ (Fin (l + 1)))
    (x : (prespectrum ((fiber f T).obj X)).space n) (t : unitInterval) :
    family f T X N G₀ G anchors (n + 1)
        ((r, z), (prespectrum ((fiber f T).obj X)).structureMap n x t) =
      (prespectrum R).structureMap n (family f T X N G₀ G anchors n ((r, z), x)) t :=
  prespectrumSimplexFamily_structure _ _ _ _ _

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputWeakZeroProduct
