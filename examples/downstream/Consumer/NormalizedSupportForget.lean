/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedRowNegativeForget

/-! Every original negative class retains forgetting with only the original finite hypotheses. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PerfectComplexes
open Quillen.PerfectComplexes.GlobalSupportedParameterCoefficient
universe u
namespace Consumer.NormalizedSupportForget

/-- Source compactness and quasi-separatedness are unnecessary for the finite class square. -/
theorem original_negative_forget
    {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace Q.left]
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) {A : AddCommGrpCat.{u + 1}}
    (g : A ⟶ (Bass.supportedNegativeKFunctor i).obj
      ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a)) :
    g ≫ (Bass.supportedNegativeKForgetNat i).app
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) ≫
      GlobalParameterCoefficient.normalizedRowNegativeClass Q i a =
    g ≫ normalizedRowNegativeClass f i a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        (ParameterTensorNormalizedRowPresentation.forget f.left
          (AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec.specUnder.obj a)) := by
  exact congrArg (fun k => g ≫ k) (normalizedRowNegativeClass_forget f i a)

end Consumer.NormalizedSupportForget
