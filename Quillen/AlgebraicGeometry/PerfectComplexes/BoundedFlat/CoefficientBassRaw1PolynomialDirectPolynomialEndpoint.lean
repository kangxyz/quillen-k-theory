/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairDirectAction
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNodeTransport

/-!
# The genuine polynomial endpoint of the direct pair action

Postcomposing the actual identity-source node with the original polynomial composite
and applying the prescribed reference normalization gives the original binary source
node. Its whole nerve point is exactly the initial point of the paused polynomial path.
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialDirectPolynomialEndpoint
open CommonReferenceNerve BassH0Merge

private theorem normalize_identity_postcomp {V W : Model.{v}} (F M : V ⟶ W)
    (h : F.functor = M.functor) :
    CommonReferenceProduct.reanchor
        (eqToIso h ≪≫ (Functor.leftUnitor M.functor).symm)
        (postcompNode M (⟨𝟙 V, Iso.refl _⟩ : Node (𝟙 V))) =
      (⟨F, Iso.refl _⟩ : Node F) := by
  have hFM : F = M := Model.Hom.ext h
  subst M
  dsimp only [CommonReferenceProduct.reanchor, postcompNode]
  apply Sigma.ext
  · exact Category.id_comp F
  apply heq_of_eq
  simp only [eqToIso_refl, isoWhiskerRight_refl, Iso.refl_trans]
  apply Iso.ext
  ext X
  change (𝟙 _ ≫ 𝟙 _) = 𝟙 _
  exact Category.comp_id _

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The actual identity-source action is exactly the complete original polynomial source node. -/
theorem polynomial_node :
    CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P p q)
      (postcompNode (BassMWholeNerve.coefficientModel P
        ((polynomialUnderFunctor R).map (p ≫ q)))
        (CoefficientBassRaw1PolynomialSourceCylinder.identityNode P a)) =
    binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map q))
      (coefficientMap P ((polynomialUnderFunctor R).map p)) 0 := by
  exact normalize_identity_postcomp
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (BassMWholeNerve.coefficientModel P ((polynomialUnderFunctor R).map (p ≫ q)))
    (CoefficientBassRaw1PolynomialRadialCaps.pairPolynomialEq P p q)

/-- The full normalized identity nerve point is the original paused polynomial path endpoint. -/
theorem polynomial_parameter :
    mapParameter (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P p q))
      (mapParameter (postcompNode (BassMWholeNerve.coefficientModel P
        ((polynomialUnderFunctor R).map (p ≫ q))))
        (CoefficientBassRaw1PolynomialSourceCylinder.identityParameter P a)) =
    CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 0 := by
  unfold CoefficientBassRaw1PolynomialSourceCylinder.identityParameter
  rw [mapParameter_parameter, mapParameter_parameter, polynomial_node]
  change parameter _ (fun _ : Fin 1 ↦ binaryNodes _ _ 0) (StdSimplex.single 0) =
    parameter _ _ (CoefficientBassRaw1PolynomialSourceAttachment.pausedBinaryParameter 0)
  rw [Path.source]
  symm
  simpa only [StdSimplex.map_single, SimplexCategory.const_apply] using
    parameter_face (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
      (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map q))
        (coefficientMap P ((polynomialUnderFunctor R).map p)))
      (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0) (StdSimplex.single 0)

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialDirectPolynomialEndpoint
