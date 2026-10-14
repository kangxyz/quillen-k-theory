/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH1References

/-! Exact outer-node normal forms of the frozen original H0 family for an arbitrary arrow. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1H0Boundary
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (w : a ⟶ b)

theorem laurent_naturality : coefficientMap P ((laurentUnderFunctor R).map w) ≫
    laurentProjection P a = laurentProjection P b ≫ coefficientMap P w :=
  coefficientTransformation_naturality P (laurentUnderCoefficient R) w

def outerIndex (i : Fin 5) : Fin 31 :=
  BassH0Diagram.plusFace.toOrderHom (ProjectionReference.sharedIndex i)

/-- Original H0 outer nodes use the actual Laurent square, independent of chart factorization. -/
theorem outer_nodes (i : Fin 5) :
    BassH0Diagram.nodes P w (outerIndex i) =
      ProjectionReference.outerNodes (coefficientMap P w)
        (coefficientMap P ((laurentUnderFunctor R).map w))
        (laurentProjection P a) (laurentProjection P b) (laurent_naturality P w) i :=
  (BassH0Diagram.plus_nodes P w (ProjectionReference.sharedIndex i)).trans
    (ProjectionReference.shared_nodes
      (polynomialProjection P a) (laurentPlus P a)
      (polynomialProjection P b) (laurentPlus P b)
      (coefficientMap P w) (coefficientMap P ((polynomialUnderFunctor R).map w))
      (coefficientMap P ((laurentUnderFunctor R).map w))
      (coefficientTransformation_naturality P (polynomialUnderCoefficient R) w)
      (coefficientTransformation_naturality P (underToLaurent R) w)
      (laurentProjection P a) (laurentProjection P b)
      (laurentPlus_projection P a) (laurentPlus_projection P b) i)

/-- The complete original normalized source node, with its original binary reference. -/
theorem source_normal : BassH0Diagram.nodes P w 2 =
    (⟨BinaryNormalizationSimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map w)) (laurentProjection P a),
      BinaryNormalizationSimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map w)) (laurentProjection P a)⟩ :
      BassH0Diagram.Node P w) :=
  outer_nodes P w 2

/-- The original full target node retains its actual Laurent naturality source transport. -/
theorem target_normal : BassH0Diagram.nodes P w 26 =
    (⟨BinaryNormalizationSimplex.targetMap (laurentProjection P b) (coefficientMap P w),
      eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
        (congrArg boundedFlatNormalizedPullback (laurent_naturality P w))) ≪≫
        BinaryNormalizationSimplex.total (laurentProjection P b) (coefficientMap P w)⟩ :
      BassH0Diagram.Node P w) :=
  outer_nodes P w 4

end Quillen.PerfectComplexes.BassH1H0Boundary
