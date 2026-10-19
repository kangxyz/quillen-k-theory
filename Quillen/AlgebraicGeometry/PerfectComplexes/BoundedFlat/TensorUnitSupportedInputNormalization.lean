/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientInputNaturality
public import Quillen.Waldhausen.SConstruction.Iterated.NormalizationTrackPasting

/-! # Actual normalization of the tensor cell on supported inputs

The original composite exact functor and the two separately normalized maps are
related by their real binary normalization track. The complete tensor-unit loop
commutes with that track by the existing normalization prism, at every spectrum
level and with both homotopy times intact.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {U X Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
  (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

/-- The original supported input map before the actual tensor coefficient operation. -/
def tensorSupportedInputPrespectrumMap :=
  exactOriginalPrespectrumMap (boundedFlatPerfectSupportedWaldhausen j)
    (boundedFlatPerfectWaldhausen Y) (tensorCoefficientSupportedForget_exact j)

/-- Tensor pullback on original supported inputs, with a single canonical composite rebase. -/
def tensorSupportedCompositePrespectrumMap :=
  exactOriginalPrespectrumMap (boundedFlatPerfectSupportedWaldhausen j)
    (boundedFlatPerfectWaldhausen X)
    ((tensorCoefficientSupportedForget_exact j).comp (boundedFlatPerfectTensorUnitPullback_exact f))

/-- The original automorphism on the true composite exact functor. -/
def tensorSupportedCompositeHomotopy :
    Homotopy (tensorSupportedCompositePrespectrumMap j f)
      (tensorSupportedCompositePrespectrumMap j f) :=
  exactOriginalPrespectrumHomotopy _ _
    ((tensorCoefficientSupportedForget_exact j).comp (boundedFlatPerfectTensorUnitPullback_exact f))
    ((tensorCoefficientSupportedForget_exact j).comp (boundedFlatPerfectTensorUnitPullback_exact f))
    (Functor.whiskerLeft (tensorCoefficientSupportedForget j)
      (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom)
    (fun _ => (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)

/-- The actual binary normalization, rather than an asserted strict composition equality. -/
def tensorSupportedInputNormalization :
    Homotopy (tensorSupportedCompositePrespectrumMap j f)
      (tensorSupportedInputPrespectrumMap j ≫ boundedFlatPerfectTensorUnitPrespectrumMap f) :=
  exactOriginalPrespectrumMapCompHomotopy _ _ _
    (tensorCoefficientSupportedForget_exact j) (boundedFlatPerfectTensorUnitPullback_exact f)

/-- Original supported input naturality is a whole normalization-relative spectrum prism. -/
def tensorSupportedInputNormalizationPasting :
    ((tensorSupportedCompositeHomotopy j f r).trans
      (tensorSupportedInputNormalization j f)).RelHomotopy
      ((tensorSupportedInputNormalization j f).trans
        (Homotopy.precomp (tensorSupportedInputPrespectrumMap j)
          (boundedFlatPerfectTensorUnitHomotopy f r))) :=
  exactNormalizationRightTrackPasting (tensorCoefficientSupportedForget_exact j)
    (boundedFlatPerfectTensorUnitPullback_exact f) (boundedFlatPerfectTensorUnitPullback_exact f)
    (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom
    (fun _ => (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)

/-- The same complete prism after the original ordinary loop-tail stabilization. -/
def tensorSupportedInputStabilizedPasting :=
  (tensorSupportedInputNormalizationPasting j f r).postcomp
    (stabilizationMap (originalPrespectrum (boundedFlatPerfectWaldhausen X)))

end Quillen.PerfectComplexes
