/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputActualFirst
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassReverseFiniteProduct
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputProjectionWord

/-! Full identity-source parameter normalization for the prescribed ordinary input cap. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputActual
open BassH0Merge CommonReferenceNerve
open BassProjectionPath.WholeReference

/-- An actual identity input node cancels only its specified full left unitor. -/
theorem identity_product_node {V W : Model.{v}} (H G : V ⟶ W)
    (θ : G.functor ≅ ((𝟙 V) ≫ H).functor) (N : Node H) :
    CommonReferenceProduct.node G (𝟙 V) H θ ⟨𝟙 V, Iso.refl _⟩ N =
      CommonReferenceProduct.reanchor (θ ≪≫ Functor.leftUnitor H.functor) N := by
  dsimp only [CommonReferenceProduct.node, CommonReferenceProduct.reanchor]
  apply Sigma.ext
  · exact Category.id_comp N.1
  apply heq_of_eq
  rw [BassReferenceMerge.composition_pair_iso, isoWhiskerRight_refl, Iso.refl_trans]
  apply Iso.ext
  ext X
  change θ.hom.app X ≫ N.2.hom.app X = (θ.hom.app X ≫ 𝟙 _) ≫ N.2.hom.app X
  rw [Category.comp_id]

/-- The finite characteristic family retains its complete nodes after identity-source removal. -/
theorem identity_product_parameter {V W : Model.{v}} (H G : V ⟶ W)
    (θ : G.functor ≅ ((𝟙 V) ≫ H).functor) {k : ℕ} (N : Fin (k + 1) → Node H)
    (z : StdSimplex ℝ (Fin (k + 1))) :
    FiniteParameter.parameter (𝟙 V) G
      (fun M i ↦ CommonReferenceProduct.node G (𝟙 V) H θ M (N i))
      (CommonReferenceNerve.parameter (𝟙 V)
        (fun _ : Fin 1 ↦ (⟨𝟙 V, Iso.refl _⟩ : Node (𝟙 V))) (StdSimplex.single 0), z) =
    mapParameter (CommonReferenceProduct.reanchor (θ ≪≫ Functor.leftUnitor H.functor))
      (CommonReferenceNerve.parameter H N z) := by
  rw [← CoefficientBassReverseFiniteProduct.finite_product_parameter_exchange]
  rw [FiniteParameter.parameter_vertex, mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun ns ↦ CommonReferenceNerve.parameter G ns z)
  funext i
  exact identity_product_node H G θ (N i)

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (p : a ⟶ b)

/-- The original polynomial-square anchor is the inverse complete fourth-node isomorphism. -/
theorem polynomial_square_base_anchor :
    FourEdge.TargetSpan.polynomialSquareBaseAnchor P p =
      (InputPolynomial.rightSquareIso P p).symm := by
  unfold InputPolynomial.rightSquareIso
  rw [NativeSquareModelNormalization.rightIso_original, Iso.trans_symm]
  rfl

/-- The complete five-node square retains the actual coefficient identity input. -/
theorem polynomial_square_identity (t : I) :
    FourEdge.TargetSpan.polynomialSquare P p (𝟙 (model P a)) (identityParameter P a, t) =
      mapParameter (CommonReferenceProduct.reanchor
        (FourEdge.TargetSpan.polynomialSquareAnchor P p (𝟙 (model P a)) ≪≫
          Functor.leftUnitor (CoefficientSquareFamilies.polynomialSource P p).functor))
        (CommonReferenceNerve.parameter (CoefficientSquareFamilies.polynomialSource P p)
          (CoefficientSquareFamilies.polynomialNodes P p) (NativeSquareFiveSimplex.parameter t)) :=
  identity_product_parameter (CoefficientSquareFamilies.polynomialSource P p) _
    (FourEdge.TargetSpan.polynomialSquareAnchor P p (𝟙 (model P a)))
    (CoefficientSquareFamilies.polynomialNodes P p) (NativeSquareFiveSimplex.parameter t)

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputActual
