/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterLaurentTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientNormalization

/-!
# Genuine tensor first rows on the literal parameter ambient Model

The product coefficient map and projected forward Laurent coordinate act on actual evaluated
complexes. Both tensor-zero faces and the independent row and automorphism grid parameters are
retained before comparison with an internal Model row.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen Quillen.Waldhausen.QuotientRows Quillen.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex Quillen.KTheory.Bass.GeometricSeedCospan

/-- The actual product scheme underlying a parameter ambient Model. -/
def scheme (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) : Scheme.{u} :=
  ((baseProductFunctor (toIntegerBase Q)).op.obj X).unop

/-- The literal product pullback induced by the original Laurent coefficient projection. -/
def coefficientMap (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    scheme Q (laurent.op.obj X) ⟶ scheme Q X :=
  ((baseProductFunctor (toIntegerBase Q)).op.map (coefficient.app X)).unop

/-- Original evaluation on the actual parameter ambient Model. -/
def evaluation (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (ParameterModels.ambient Q).obj X ⥤ BoundedFlatPerfect (scheme Q X) :=
  globalEvaluation ((baseProductFunctor (toIntegerBase Q)).op.obj X)

/-- Pull back the evaluated input and apply genuine tensor to the first coefficient row. -/
def firstRow (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  evaluation Q X ⋙ boundedFlatPerfectPullback (coefficientMap Q X) ⋙
    boundedFlatPerfectTensorUnitFirstRow (scheme Q (laurent.op.obj X))

/-- Both original diagonal tensor entries are zero objects. -/
theorem firstRow_zero (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    (K : (ParameterModels.ambient Q).obj X) (i : Fin 2) :
    IsZero (((boundedFlatPerfectTensorUnitRows (scheme Q (laurent.op.obj X))).obj
      ((boundedFlatPerfectPullback (coefficientMap Q X)).obj
        ((evaluation Q X).obj K))).obj (interval i i le_rfl)) :=
  boundedFlatPerfectTensorUnitRows_zero _ _ i

/-- The actual row normalization retains the original tensor-zero comparisons. -/
def firstRowNormalization (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    firstRow Q X ≅ evaluation Q X ⋙
      tensorUnitPullbackNormalizedFunctor (coefficientMap Q X) ⋙
        oneEmbedding (boundedFlatPerfectWaldhausen (scheme Q (laurent.op.obj X))) :=
  Functor.isoWhiskerLeft (evaluation Q X)
    (tensorUnitPullbackFirstRowNormalization (coefficientMap Q X))

/-- Forward multiplication by the original projected Laurent unit on the genuine tensor row. -/
def firstRowUnit (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  Functor.isoWhiskerLeft (evaluation Q X)
    (Functor.isoWhiskerLeft (boundedFlatPerfectPullback (coefficientMap Q X))
      (tensorUnitFirstRowAutomorphism (scheme Q (laurent.op.obj X))
        (ParameterLaurentUnit.projectedLaurentScalar Q X)))

/-- Whole finite-grid normalization retains separate automorphism and first-row coordinates. -/
theorem prism (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    {k n m : SimplexCategory}
    (A : Grid₂ n m ⥤ (ParameterModels.ambient Q).obj X)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    tensorUnitPullbackNormalizedCoefficientPrism (coefficientMap Q X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X) (A ⋙ evaluation Q X) τ θ =
      nerveCylinderDiagram (Functor.whiskerLeft (A ⋙ evaluation Q X)
        (normalizedWeakTransformation
          (boundedFlatPerfectTensorUnitPullback_exact (coefficientMap Q X))
          (boundedFlatPerfectTensorUnitPullback_exact (coefficientMap Q X))
          (boundedFlatPerfectTensorUnitPullbackAutomorphism (coefficientMap Q X)
            (ParameterLaurentUnit.projectedLaurentScalar Q X)).hom)) τ ⋙
        suspensionRow (boundedFlatPerfectWaldhausen (scheme Q (laurent.op.obj X))) θ :=
  tensorUnitPullbackNormalizedCoefficientPrism_eq _ _ _ τ θ

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
