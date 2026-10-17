/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCompositeEndpoint

/-!
# The genuine polynomial endpoint of the composite pair action

Postcomposing the actual identity-source node by the two original polynomial maps
and applying the prescribed reference normalization gives the original binary terminal
node. Its whole nerve point is exactly the terminal point of the paused polynomial path.
-/
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCompositePolynomialEndpoint
open CommonReferenceNerve BassH0Merge

private theorem normalize_identity_postcomp {V W T : Model.{v}}
    (F : V ⟶ T) (M : V ⟶ W) (K : W ⟶ T) (η : F.functor ≅ (M ≫ K).functor) :
    CommonReferenceProduct.reanchor
        (η ≪≫ isoWhiskerRight (Functor.leftUnitor M.functor).symm K.functor)
        (postcompNode K (postcompNode M (⟨𝟙 V, Iso.refl _⟩ : Node (𝟙 V)))) =
      (⟨M ≫ K, η⟩ : Node F) := by
  dsimp only [CommonReferenceProduct.reanchor, postcompNode]
  apply Sigma.ext
  · exact congrArg (fun H ↦ H ≫ K) (Category.id_comp M)
  apply heq_of_eq
  apply Iso.ext
  ext X
  simp only [Iso.trans_hom, isoWhiskerRight_hom, Iso.symm_hom, NatTrans.comp_app,
    whiskerRight_app, leftUnitor_inv_app, isoWhiskerRight_refl, Iso.refl_hom,
    NatTrans.id_app, CategoryTheory.Functor.map_id]
  change (η.hom.app X ≫ 𝟙 _) ≫
    CategoryTheory.Functor.map K.functor (𝟙 (M.functor.obj X)) = η.hom.app X
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  exact Category.comp_id _

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The actual iterated identity-source action is exactly the complete binary terminal node. -/
theorem polynomial_node :
    CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialCompositeEndpoint.polynomialIso P p q)
      (postcompNode (CoefficientBassSeedTargetChartAttachment.M P q)
        (postcompNode (CoefficientBassSeedTargetChartAttachment.M P p)
          (CoefficientBassRaw1PolynomialSourceCylinder.identityNode P a))) =
    binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map q))
      (coefficientMap P ((polynomialUnderFunctor R).map p)) 2 := by
  exact normalize_identity_postcomp
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassSeedTargetChartAttachment.M P p)
    (CoefficientBassSeedTargetChartAttachment.M P q)
    (BinaryNormalizationSimplex.total
      (coefficientMap P ((polynomialUnderFunctor R).map q))
      (coefficientMap P ((polynomialUnderFunctor R).map p)))

/-- The full normalized iterated identity nerve point is the paused polynomial terminal point. -/
theorem polynomial_parameter :
    mapParameter (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialCompositeEndpoint.polynomialIso P p q))
      (mapParameter (postcompNode (CoefficientBassSeedTargetChartAttachment.M P q))
        (mapParameter (postcompNode (CoefficientBassSeedTargetChartAttachment.M P p))
          (CoefficientBassRaw1PolynomialSourceCylinder.identityParameter P a))) =
    CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1 := by
  unfold CoefficientBassRaw1PolynomialSourceCylinder.identityParameter
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter, polynomial_node]
  change parameter _ (fun _ : Fin 1 ↦ binaryNodes _ _ 2) (StdSimplex.single 0) =
    parameter _ _ (CoefficientBassRaw1PolynomialSourceAttachment.pausedBinaryParameter 1)
  rw [Path.target]
  symm
  simpa only [StdSimplex.map_single, SimplexCategory.const_apply] using
    parameter_face (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
      (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map q))
        (coefficientMap P ((polynomialUnderFunctor R).map p)))
      (SimplexCategory.const ⦋0⦌ ⦋2⦌ 2) (StdSimplex.single 0)

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCompositePolynomialEndpoint
