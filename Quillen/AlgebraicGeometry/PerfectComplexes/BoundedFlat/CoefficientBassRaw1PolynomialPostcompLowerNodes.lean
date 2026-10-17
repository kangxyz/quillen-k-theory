/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPostcompAnchor

/-! Full lower nodes of the original postcomposed cap in the fixed Laurent triple. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleAnchor
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
private theorem postcomp_lower_node_of_word
    {V₀ V₁ W₀ W₁ : Model.{u}} (A : V₀ ⟶ V₁) (F : V₁ ⟶ W₀)
    (L : W₀ ⟶ W₁) (D : V₀ ⟶ W₀) (T : V₀ ⟶ W₁) (G : V₁ ⟶ W₁)
    (ε : D.functor ≅ (A ≫ F).functor)
    (η : T.functor ≅ (D ≫ L).functor)
    (κ : T.functor ≅ (A ≫ G).functor)
    (ρ : G.functor ≅ (F ≫ L).functor)
    (h : η ≪≫ isoWhiskerRight ε L.functor = κ ≪≫ isoWhiskerLeft A.functor ρ)
    (N : Node F) :
    CommonReferenceProduct.reanchor η
      (postcompNode L (CommonReferenceProduct.reanchor ε (precompNode A N))) =
    CommonReferenceProduct.reanchor κ
      (precompNode A (CommonReferenceProduct.reanchor ρ (postcompNode L N))) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  dsimp only [CommonReferenceProduct.reanchor, postcompNode, precompNode]
  rw [isoWhiskerRight_trans, isoWhiskerLeft_trans, ← Iso.trans_assoc,
    ← Iso.trans_assoc, h]
  rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The exact chart-action reference of the postcomposed cap before evaluation. -/
def postcompLowerIso :=
  isoWhiskerRight (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w)
      (BassH0Merge.normalizedMap (chart P β d)).functor ≪≫
    (isoWhiskerLeft (CoefficientBassRaw1PolynomialPostcomp.pair P p q).functor
      (binaryChartIso P β w)).symm

/-- Every full lower node lies in the prescribed Laurent triple with its original anchor. -/
theorem postcomp_lower_node
    (N : Node (CoefficientBassLaurentCompositionCarrier.reference P p q)) :
    CommonReferenceProduct.reanchor (postcompLowerIso P β p q w)
      (postcompNode (BassH0Merge.normalizedMap (laurentArrow P w))
        (CommonReferenceProduct.reanchor
          (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β p q)
          (precompNode (BassMWholeNerve.coefficientModel P (β.app a)) N))) =
    CommonReferenceProduct.reanchor (referenceIso P β p q w).symm
      (precompNode (BassMWholeNerve.coefficientModel P (β.app a))
        (CommonReferenceProduct.reanchor
          (NormalizedTripleSimplex.leftFirst
            (laurentArrow P w) (laurentArrow P q) (laurentArrow P p))
          (postcompNode (BassH0Merge.normalizedMap (laurentArrow P w)) N))) := by
  apply postcomp_lower_node_of_word
    (BassMWholeNerve.coefficientModel P (β.app a))
    (CoefficientBassLaurentCompositionCarrier.reference P p q)
    (BassH0Merge.normalizedMap (laurentArrow P w)) _ _ _
    (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β p q)
    (postcompLowerIso P β p q w) (referenceIso P β p q w).symm
    (NormalizedTripleSimplex.leftFirst
      (laurentArrow P w) (laurentArrow P q) (laurentArrow P p))
    _ N
  have h := postcomp_word P β p q w
  dsimp only [postcompLowerIso, BassMWholeNerve.coefficientModel,
    CoefficientBassLaurentCompositionCarrier.reference,
    CoefficientBassLaurentCompositionCarrier.first,
    CoefficientBassLaurentCompositionCarrier.second,
    chart, laurentArrow] at h ⊢
  exact h

/-- The same full reference equality holds on every point of the original lower nerve. -/
theorem postcomp_lower_parameter
    (y : |parameterSSet (CoefficientBassLaurentCompositionCarrier.reference P p q)|) :
    mapParameter (fun N : Node (CoefficientBassLaurentCompositionCarrier.reference P p q) ↦
    CommonReferenceProduct.reanchor (postcompLowerIso P β p q w)
      (postcompNode (BassH0Merge.normalizedMap (laurentArrow P w))
        (CommonReferenceProduct.reanchor
          (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β p q)
          (precompNode (BassMWholeNerve.coefficientModel P (β.app a)) N)))) y =
    mapParameter (fun N : Node (CoefficientBassLaurentCompositionCarrier.reference P p q) ↦
    CommonReferenceProduct.reanchor (referenceIso P β p q w).symm
      (precompNode (BassMWholeNerve.coefficientModel P (β.app a))
        (CommonReferenceProduct.reanchor
          (NormalizedTripleSimplex.leftFirst
            (laurentArrow P w) (laurentArrow P q) (laurentArrow P p))
          (postcompNode (BassH0Merge.normalizedMap (laurentArrow P w)) N)))) y := by
  exact congrArg (fun g ↦ mapParameter g y)
    (funext (postcomp_lower_node P β p q w))

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleAnchor
