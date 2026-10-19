/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterLaurentTrack
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedCoefficientNormalization

/-!
# Genuine tensor first rows on the literal supported parameter Model

Evaluation lands in the original supported category. Pullback uses the actual product open-pair
square, after which tensor is applied internally to both zero faces and the middle complex.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen Quillen.Waldhausen.QuotientRows Quillen.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace Quillen.PerfectComplexes.ParameterTensorSupportedRow
open GlobalSectionChangeIndex Quillen.KTheory.Bass.GeometricSeedCospan
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The actual supported product pair at a scheme parameter. -/
def pair (X : Scheme.{u}ᵒᵖ) := GlobalSupportedParameter.pair f X.unop

/-- The original Laurent projection induces this full open-pair square. -/
def coefficientPair (X : Scheme.{u}ᵒᵖ) : pair f (laurent.op.obj X) ⟶ pair f X :=
  GlobalSupportedParameter.pairMap f (coefficient.app X).unop

/-- Evaluation of the literal supported parameter Model in its original supported complexes. -/
def evaluation (X : Scheme.{u}ᵒᵖ) :
    (ParameterModels.supported f).obj X ⥤
      (boundedFlatPerfectSupported (pair f X).obj.hom).FullSubcategory :=
  supportedEvaluation (pair f X).obj.hom

/-- The independently constructed first row remains inside the supported target. -/
def firstRow (X : Scheme.{u}ᵒᵖ) :=
  evaluation f X ⋙ boundedFlatPerfectSupportedPullback (coefficientPair f X) ⋙
    boundedFlatPerfectSupportedTensorUnitFirstRow (pair f (laurent.op.obj X)).obj.hom

/-- Both original tensor diagonal entries are genuine zero objects of the supported category. -/
theorem firstRow_zero (X : Scheme.{u}ᵒᵖ)
    (K : (ParameterModels.supported f).obj X) (i : Fin 2) :
    IsZero (((boundedFlatPerfectSupportedTensorUnitRows
      (pair f (laurent.op.obj X)).obj.hom).obj
      ((boundedFlatPerfectSupportedPullback (coefficientPair f X)).obj
        ((evaluation f X).obj K))).obj (interval i i le_rfl)) :=
  boundedFlatPerfectSupportedTensorUnitRows_zero _ _ i

/-- The actual row normalization retains both original tensor-zero comparisons. -/
def firstRowNormalization (X : Scheme.{u}ᵒᵖ) :
    firstRow f X ≅ evaluation f X ⋙
      tensorSupportedPairNormalizedFunctor (coefficientPair f X) ⋙
        oneEmbedding (boundedFlatPerfectSupportedWaldhausen
          (pair f (laurent.op.obj X)).obj.hom) :=
  Functor.isoWhiskerLeft (evaluation f X)
    (tensorSupportedPairFirstRowNormalization (coefficientPair f X))

/-- Forward multiplication by the original projected Laurent unit inside the supported row. -/
def firstRowUnit (X : Scheme.{u}ᵒᵖ) :=
  Functor.isoWhiskerLeft (evaluation f X)
    (Functor.isoWhiskerLeft (boundedFlatPerfectSupportedPullback (coefficientPair f X))
      (supportedTensorUnitFirstRowAutomorphism (pair f (laurent.op.obj X)).obj.hom
        (ParameterLaurentUnit.projectedLaurentScalar Q X)))

/-- The whole first supported coefficient prism retains independent unit and row coordinates. -/
theorem prism (X : Scheme.{u}ᵒᵖ) {k n m : SimplexCategory}
    (A : Grid₂ n m ⥤ (ParameterModels.supported f).obj X)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    tensorSupportedPairNormalizedCoefficientPrism (coefficientPair f X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X) (A ⋙ evaluation f X) τ θ =
      nerveCylinderDiagram (Functor.whiskerLeft (A ⋙ evaluation f X)
        (normalizedWeakTransformation
          (tensorSupportedPair_exact (coefficientPair f X))
          (tensorSupportedPair_exact (coefficientPair f X))
          (tensorSupportedPairAutomorphism (coefficientPair f X)
            (ParameterLaurentUnit.projectedLaurentScalar Q X)).hom)) τ ⋙
        suspensionRow (boundedFlatPerfectSupportedWaldhausen
          (pair f (laurent.op.obj X)).obj.hom) θ :=
  tensorSupportedPairNormalizedCoefficientPrism_eq _ _ _ τ θ

end Quillen.PerfectComplexes.ParameterTensorSupportedRow
