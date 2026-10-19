/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedRowNegativeForget

/-! The actual normalized forget map retains empty support and degree-zero Model classes. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.PerfectComplexes
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
universe u
namespace QuillenTest.NormalizedSupportForget

/-- Empty support is forgotten stably at every original scheme parameter. -/
theorem bottom_forget (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (ParameterTensorNormalizedRowPresentation.forget (⊥ : Q.Opens).ι X) :=
  ParameterTensorNormalizedRowPresentation.bottom_forget_stable Q X

/-- The original degree-zero Model class is retained without a compactness premise. -/
theorem zero_class {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) (x : ((ParameterModels.supported f).obj X).waldhausen.K 0) :
    (stableHomotopyFunctor (0 : ℤ)).map (ParameterTensorNormalizedRowPresentation.forget f X)
      (Quillen.KTheory.Bass.SchemeModelRowSeed.normalizedModelClass (ParameterModels.supported f)
        (ParameterLaurentTrack.supportedUnit f) (ParameterLaurentTrack.supportedUnit_naturality f)
        X 0 x) =
    Quillen.KTheory.Bass.SchemeModelRowSeed.normalizedModelClass (ParameterModels.ambient Q)
      (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q) X 0
      (Quillen.Waldhausen.KMap ((ParameterModels.forget f).app X).exact 0 x) :=
  ParameterTensorNormalizedRowPresentation.modelClass_forget f X 0 x

end QuillenTest.NormalizedSupportForget
