/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OriginalUnitSquareSimplex
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientPolynomialSpanUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionPath
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexLiftSquareOperations
public import Quillen.Waldhausen.SConstruction.Iterated.RealizationSimplexComposition

/-! Original normalized identity and the three actual moving pieces of the polynomial-span
unit after the Bass comparison. The square pieces and product retain all native parameters. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientPolynomialSpanUnitSimplex
open OriginalUnitSquareSimplex

/-- Three actual original identity-track vertices, including the rebased identity intermediate. -/
def identityVertices (X : Scheme.{u}) : Fin 3 →
    (modelOf (boundedFlatPerfectWaldhausen X) ⟶ modelOf (boundedFlatPerfectWaldhausen X)) :=
  ![unitSourceMap X, unitIntermediateMap X, unitTargetMap X]

def identityReferences (X : Scheme.{u}) : ∀ i,
    (unitSourceMap X).functor ≅ (identityVertices X i).functor :=
  Fin.cases (Iso.refl _) (Fin.cases (unitFirst X)
    (Fin.cases (unitFirst X ≪≫ unitSecond X) (fun i ↦ Fin.elim0 i)))

def identitySimplex (X : Scheme.{u}) : ModelSimplex
    (modelOf (boundedFlatPerfectWaldhausen X)) (modelOf (boundedFlatPerfectWaldhausen X)) 2 :=
  ModelSimplex.ofIsos (unitSourceMap X) (identityVertices X) (identityReferences X)

/-- Both exact normalization components, not an arbitrary path between equal endpoints. -/
theorem identitySimplex_triangle (X : Scheme.{u}) : identitySimplex X =
    ModelSimplex.triangle (unitFirst X).hom (unitSecond X).hom
      (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
      (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance) := by
  have h : identitySimplex X = (identitySimplex X).face (𝟙 ⦋2⦌) :=
    ModelSimplex.ext_diagram (by rfl)
  rw [h]
  unfold identitySimplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · rfl

private theorem family_simplex_congr {V W : Model.{u}} {k : ℕ}
    (S T : ModelSimplex V W k) (h : S = T) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily S n (z, x) = prespectrumSimplexFamily T n (z, x) :=
  congrArg (fun U ↦ prespectrumSimplexFamily U n (z, x)) h

private theorem family_parameter_congr {V W : Model.{u}} {k : ℕ}
    (S : ModelSimplex V W k) (n : ℕ)
    (z w : StdSimplex ℝ (Fin (k + 1))) (h : z = w) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily S n (z, x) = prespectrumSimplexFamily S n (w, x) :=
  congrArg (fun v ↦ prespectrumSimplexFamily S n (v, x)) h

/-- The entire original identity triangle, with its independent comparison and path times. -/
theorem identity_triangle_native (X : Scheme.{u}) (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    prespectrumSimplexFamily (identitySimplex X) n
      (Quillen.TheoremB.compositionTriangleHomotopy (r, s), x) =
      (boundedFlatNormalizedIdTrackComparison X).level n (r, (s, x)) := by
  refine (family_simplex_congr _ _ (identitySimplex_triangle X) n _ x).trans ?_
  refine (prespectrumSimplexFamily_triangle (unitFirst X).hom (unitSecond X).hom
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
    n r s x).trans ?_
  exact (Homotopy.RelHomotopy.level_eq_apply _ _ n (unit_native_level X n) r s x).symm

private theorem identity_parameter_target (s : unitInterval) :
    Quillen.TheoremB.compositionTriangleHomotopy (1, s) = binaryPath (k := 2) 0 1 2 s := by
  have h := (triangle (𝟙 ⦋2⦌)).apply_one s
  change StdSimplex.map id (Quillen.TheoremB.compositionTriangleHomotopy (1, s)) =
    binaryPath (k := 2) 0 1 2 s at h
  simpa only [StdSimplex.map_id] using h

/-- Every point of the unchanged split geometric identity track is an explicit scalar path. -/
theorem identity_native (X : Scheme.{u}) :
    PathLift (identitySimplex X) (binaryPath (k := 2) 0 1 2)
      (boundedFlatPerfectPrespectrumIdHomotopy X) := by
  intro n s x
  exact (family_parameter_congr (identitySimplex X) n _ _
    (identity_parameter_target s).symm x).trans
      ((identity_triangle_native X n 1 s x).trans
        (((boundedFlatNormalizedIdTrackComparison X).level n).apply_one (s, x)))

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The positive moving piece is the original polynomial unit square postcomposed unchanged. -/
def plusSimplex := (OriginalUnitSquareSimplex.simplex (polynomialProjection P a)).postcomp
  (sourceMap (laurentPlus P a))

/-- The negative moving piece retains its separate actual Laurent chart. -/
def minusSimplex := (OriginalUnitSquareSimplex.simplex (polynomialProjection P a)).postcomp
  (sourceMap (laurentMinus P a))

theorem plus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (plusSimplex P a) n (squareParameter (r, s), x) =
      ((boundedFlatCoefficientPolynomialIdentitySquare P a).postcompose
        (boundedFlatPerfectPrespectrumMap (laurentPlus P a))).level n (r, (s, x)) := by
  refine (prespectrumSimplexFamily_postcomp
    (OriginalUnitSquareSimplex.simplex (polynomialProjection P a))
    (sourceMap (laurentPlus P a)) n (squareParameter (r, s)) x).trans ?_
  exact congrArg ((boundedFlatPerfectPrespectrumMap (laurentPlus P a)).map n)
    (square_native (polynomialProjection P a) n r s x)

theorem minus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (minusSimplex P a) n (squareParameter (r, s), x) =
      ((boundedFlatCoefficientPolynomialIdentitySquare P a).postcompose
        (boundedFlatPerfectPrespectrumMap (laurentMinus P a))).level n (r, (s, x)) := by
  refine (prespectrumSimplexFamily_postcomp
    (OriginalUnitSquareSimplex.simplex (polynomialProjection P a))
    (sourceMap (laurentMinus P a)) n (squareParameter (r, s)) x).trans ?_
  exact congrArg ((boundedFlatPerfectPrespectrumMap (laurentMinus P a)).map n)
    (square_native (polynomialProjection P a) n r s x)

/-- The moving middle is the actual fifteen-vertex composite grid, retaining both times. -/
def middleSimplex := CommonReferenceProduct.simplex
  (unitSourceMap (space (op P, a))) (identityVertices (space (op P, a)))
  (identityReferences (space (op P, a)))
  (BassProjectionPath.source P a) (fun i ↦ (BassProjectionPath.nodes P a i).1)
  (fun i ↦ (BassProjectionPath.nodes P a i).2)

def middleParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 15)) :=
  ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 2 4
    (binaryPath (k := 2) 0 1 2 z.1, BassProjectionPath.parameter z.2), by fun_prop⟩

/-- The actual moving overlap is the product of the original base identity and Bass cylinder. -/
theorem middle_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (middleSimplex P a) n (middleParameter.{u} (r, s), x) =
      (boundedFlatCoefficientBassSquareComparison P a).map n
        (HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n
          (s, (boundedFlatCoefficientIdentityHomotopy P a).level n (r, x))) := by
  refine (CommonReferenceProduct.prespectrum_comp
    (unitSourceMap (space (op P, a))) (identityVertices (space (op P, a)))
    (identityReferences (space (op P, a)))
    (BassProjectionPath.source P a) (fun i ↦ (BassProjectionPath.nodes P a i).1)
    (fun i ↦ (BassProjectionPath.nodes P a i).2) n x
    (binaryPath (k := 2) 0 1 2 r) (BassProjectionPath.parameter s)).trans ?_
  refine (congrArg (fun y ↦ prespectrumSimplexFamily (BassProjectionPath.simplex P a) n
    (BassProjectionPath.parameter s, y)) (identity_native (space (op P, a)) n r x)).trans ?_
  exact BassProjectionPath.native P a n s
    ((boundedFlatCoefficientIdentityHomotopy P a).level n (r, x))

end Quillen.PerfectComplexes.CoefficientPolynomialSpanUnitSimplex
