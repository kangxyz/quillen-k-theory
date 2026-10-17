/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedKZeroComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassKZeroComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.Bass.SupportedForget

/-!
# The original supported-to-ambient map at the native zero bottom

The actual supported evaluation square preserves the original support inclusion on every
K-group. At degree zero it compares the existing supported and ambient finite-bottom
isomorphisms, including the ambient normalized perfect evaluation. Only ambient compactness
is needed. No injectivity of the support-forgetting map is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The actual evaluation square preserves the bounded-flat support inclusion on all K-groups. -/
theorem boundedFlatCoefficientSupportedSectionKEquiv_forget (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedModel f a).waldhausen.K n) :
    boundedFlatCoefficientSectionKEquiv (op Q, a) n
        (KMap (boundedFlatCoefficientSupportedForgetModelMap f a).exact n x) =
      boundedFlatPerfectSupportedKMap (schemeMap f a) n
        (boundedFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n x) := by
  exact boundedFlatCoefficientEvaluationKEquiv_natural
    (boundedFlatCoefficientSupportedSectionWaldhausen (schemeMap f a))
    (boundedFlatPerfectSupportedWaldhausen (schemeMap f a))
    (boundedFlatCoefficientSupportedSectionEquivalence (schemeMap f a))
    (boundedFlatCoefficientSupportedSectionEquivalence_functor_exact (schemeMap f a))
    (boundedFlatCoefficientSupportedSectionEquivalence_inverse_exact (schemeMap f a))
    (boundedFlatCoefficientSectionWaldhausen (op Q, a))
    (boundedFlatPerfectWaldhausen (space (op Q, a)))
    (boundedFlatCoefficientSectionEquivalence (op Q, a))
    (boundedFlatCoefficientOriginalEvaluation_exact (op Q, a))
    (boundedFlatCoefficientSectionEquivalence_inverse_exact (op Q, a))
    (boundedFlatCoefficientSupportedForgetModelMap f a).exact
    (subcategoryInclusion_exact _ _ (fun _ h ↦ h.1))
    (by
      simp only [boundedFlatCoefficientSupportedSectionEquivalence_functor]
      exact eqToIso (boundedFlatCoefficientSupportedEvaluation_forget_to_boundedFlat f a).symm)
    n x

variable [CompactSpace Q.left]

/-- The literal original perfect support inclusion commutes with the existing K-equivalences. -/
theorem boundedFlatCoefficientSupportedPerfectKEquiv_forget (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedModel f a).waldhausen.K n) :
    boundedFlatCoefficientSectionPerfectKEquiv (op Q, a) n
        (KMap (boundedFlatCoefficientSupportedForgetModelMap f a).exact n x) =
      perfectSupportedKMap (schemeMap f a) n
        (boundedFlatCoefficientSupportedPerfectKEquiv f a n x) := by
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  rw [boundedFlatCoefficientSectionPerfectKEquiv_apply,
    boundedFlatCoefficientSupportedSectionKEquiv_forget]
  exact (DFunLike.congr_fun (boundedFlatPerfectSupportedToPerfectSupported_comp
    (schemeMap f a) n) (boundedFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n x)).symm

/-- The original zero-bottom comparisons retain the actual supported-to-ambient model map. -/
@[reassoc]
theorem boundedFlatCoefficientSupportedBassBottomZeroIso_forget (a : Under R) :
    Bass.supportedKZeroForget.app ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) ≫
        (boundedFlatCoefficientAmbientBassBottomZeroNatIso Q).hom.app a =
      (boundedFlatCoefficientSupportedBassBottomZeroIso f a).hom ≫
        (stableHomotopyFunctor 0).map ((boundedFlatCoefficientSupportedBassForget f 0).app a) := by
  let : IsIso ((stableHomotopyFunctor 0).map
      (boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op Q, a))) :=
    boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap_isStableEquivalence (op Q, a) 0
  apply (cancel_mono ((stableHomotopyFunctor 0).map
    (boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op Q, a)))).mp
  rw [Category.assoc, boundedFlatCoefficientAmbientBassBottomZeroNatIso_evaluation]
  ext x
  obtain ⟨y, hy⟩ := (boundedFlatCoefficientSupportedPerfectKEquiv f a 0).surjective x.toMul
  change originalKStableEquiv (perfectWaldhausen (space (op Q, a))) 0
      (Additive.ofMul (perfectSupportedKMap (schemeMap f a) 0 x.toMul)) =
    (stableHomotopyFunctor 0).map
      (boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op Q, a))
      ((stableHomotopyFunctor 0).map
        (prespectrumMap (boundedFlatCoefficientSupportedForgetModelMap f a))
        (modelKStableEquiv (boundedFlatCoefficientSupportedModel f a) 0
          (Additive.ofMul ((boundedFlatCoefficientSupportedPerfectKEquiv f a 0).symm x.toMul))))
  rw [← hy, MulEquiv.symm_apply_apply]
  exact (congrArg (fun z ↦ originalKStableEquiv (perfectWaldhausen (space (op Q, a))) 0
      (Additive.ofMul z)) (boundedFlatCoefficientSupportedPerfectKEquiv_forget f a 0 y).symm).trans
    (boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap_KEquiv (op Q, a) 0
      (KMap (boundedFlatCoefficientSupportedForgetModelMap f a).exact 0 y) |>.trans
        (congrArg ((stableHomotopyFunctor 0).map
          (boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op Q, a)))
          (modelKStableEquiv_naturality (boundedFlatCoefficientSupportedForgetModelMap f a) 0 y)))

end Quillen.PerfectComplexes
