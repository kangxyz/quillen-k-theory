/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedBasicLocalization
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryNormalizedRowConnecting

/-! # The intrinsic basic normalized boundary at the original integral Spec parameters -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace Quillen.PerfectComplexes.ParameterNormalizedBasicLocalization
open GlobalSectionChangeIndex ParameterAuxiliarySupport
open ParameterAuxiliaryNormalizedRowLocalization
variable (Q : Scheme.{u}) (U : Q.Opens)

/-- The actual basic open inclusion with its canonical integral-base structure. -/
abbrev basicOverInclusion :
    Over.mk (toIntegerBase U.toScheme) ⟶ Over.mk (toIntegerBase Q) :=
  Over.homMk U.ι (toIntegerBase_naturality U.ι)

instance basicOverInclusion_isOpenImmersion : IsOpenImmersion (basicOverInclusion Q U).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

/-- The canonical integral-base object retains the original compact space. -/
theorem basicOver_compactSpace (X : Scheme.{u}) [CompactSpace X] :
    CompactSpace (Over.mk (toIntegerBase X)).left :=
  inferInstanceAs (CompactSpace X)

/-- The canonical integral-base object retains the original quasi-separated space. -/
theorem basicOver_quasiSeparatedSpace (X : Scheme.{u}) [QuasiSeparatedSpace X] :
    QuasiSeparatedSpace (Over.mk (toIntegerBase X)).left :=
  inferInstanceAs (QuasiSeparatedSpace X)

attribute [local instance] basicOver_compactSpace basicOver_quasiSeparatedSpace

variable [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U]

/-- The actual basic fiber lift is stable at every original integral Spec parameter. -/
theorem basicLift_spec_isStableEquivalence (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (basicLift Q U (specUnder.obj a)) := by
  let f := basicOverInclusion Q U
  exact (auxiliary_basic_lift_stable_iff Q U (specUnder.obj a)).mp
    (normalizedPresentationLift_spec_isStableEquivalence f ⊥ a)

/-- This is the basic row's own boundary, evaluated at the original Spec parameter. -/
def basicSpecConnecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup (ParameterTensorNormalizedRowPresentation.ambient U.toScheme
      (specUnder.obj a)) (d + 1) ⟶
    stableHomotopyGroup (ParameterTensorNormalizedRowPresentation.supported U.ι
      (specUnder.obj a)) d := by
  have : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift (restriction U.ι (specUnder.obj a))
        (ParameterTensorNormalizedRowPresentation.forget U.ι (specUnder.obj a))
        (basicNull Q U (specUnder.obj a)))) :=
    basicLift_spec_isStableEquivalence Q U a d
  exact stableFiberLiftConnecting
    (ParameterTensorNormalizedRowPresentation.forget U.ι (specUnder.obj a))
    (restriction U.ι (specUnder.obj a)) (basicNull Q U (specUnder.obj a)) d

/-- The whole original auxiliary null compares both intrinsic Spec-parameter boundaries. -/
theorem auxiliary_basic_spec_connecting
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    normalizedPresentationConnecting
        (basicOverInclusion Q U) ⊥ a d ≫
      (stableHomotopyFunctor d).map (basicSourceIso Q U (specUnder.obj a)).hom =
    (stableHomotopyFunctor (d + 1)).map
        (ParameterTensorNormalizedRowPresentation.forget (inverseOpen U.ι ⊥).ι
          (specUnder.obj a)) ≫ basicSpecConnecting Q U a d := by
  let f := basicOverInclusion Q U
  have : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift (normalizedPresentationRestriction U.ι ⊥ (specUnder.obj a))
        (normalizedPresentationEnlargement U.ι ⊥ (specUnder.obj a))
        (normalizedPresentationNull U.ι ⊥ (specUnder.obj a)))) :=
    normalizedPresentationLift_spec_isStableEquivalence f ⊥ a d
  have : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift (restriction U.ι (specUnder.obj a))
        (ParameterTensorNormalizedRowPresentation.forget U.ι (specUnder.obj a))
        (basicNull Q U (specUnder.obj a)))) :=
    basicLift_spec_isStableEquivalence Q U a d
  exact stableFiberLiftConnecting_naturality
    (normalizedPresentationEnlargement U.ι ⊥ (specUnder.obj a))
    (normalizedPresentationRestriction U.ι ⊥ (specUnder.obj a))
    (ParameterTensorNormalizedRowPresentation.forget U.ι (specUnder.obj a))
    (restriction U.ι (specUnder.obj a))
    (normalizedPresentationNull U.ι ⊥ (specUnder.obj a)) (basicNull Q U (specUnder.obj a))
    (basicSourceIso Q U (specUnder.obj a)).hom
    (ParameterTensorNormalizedRowPresentation.forget (⊥ : Q.Opens).ι (specUnder.obj a))
    (ParameterTensorNormalizedRowPresentation.forget (inverseOpen U.ι ⊥).ι (specUnder.obj a))
    ((enlargement_forget U.ι ⊥ (specUnder.obj a)).trans
      (basicSourceIso_forget Q U (specUnder.obj a)).symm)
    (restriction_forget U.ι ⊥ (specUnder.obj a)).symm
    (basicNull_comparison Q U (specUnder.obj a)) d

end Quillen.PerfectComplexes.ParameterNormalizedBasicLocalization
