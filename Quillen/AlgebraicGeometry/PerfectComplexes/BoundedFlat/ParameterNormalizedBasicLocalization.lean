/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedBasicDiagram
public import Quillen.Topology.Prespectrum.FiberLiftConnecting

/-!
# The actual basic normalized-row localization and its intrinsic boundary

The source is supported on the original displayed open U, and the middle and
open objects are the actual ambient normalized rows. Actual empty-support
forget maps and the original whole null transport the auxiliary fiber lift.
The basic boundary is defined from its own path-space fiber lift.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.Products
universe u
namespace Quillen.PerfectComplexes.ParameterNormalizedBasicLocalization
open GlobalSectionChangeIndex ParameterAuxiliarySupport
open ParameterAuxiliaryNormalizedRowLocalization
variable (Q : Scheme.{u}) (U : Q.Opens) (X : Scheme.{u}ᵒᵖ)

/-- The displayed basic maps and their prescribed whole null define the actual path-space lift. -/
def basicLift := homotopyFiberLift (restriction U.ι X)
  (ParameterTensorNormalizedRowPresentation.forget U.ι X) (basicNull Q U X)

/-- The actual empty-support maps preserve the whole original auxiliary path-space lift. -/
theorem auxiliary_basic_lift_square :
    ParameterAuxiliaryNormalizedRowLocalization.normalizedPresentationLift U.ι ⊥ X ≫
      homotopyFiberMap (Arrow.homMk
        (f := Arrow.mk (normalizedPresentationRestriction U.ι ⊥ X))
        (g := Arrow.mk (restriction U.ι X))
        (ParameterTensorNormalizedRowPresentation.forget (⊥ : Q.Opens).ι X)
        (ParameterTensorNormalizedRowPresentation.forget (inverseOpen U.ι ⊥).ι X)
        (restriction_forget U.ι ⊥ X).symm) =
      (basicSourceIso Q U X).hom ≫ basicLift Q U X :=
  homotopyFiberLift_naturality
    (normalizedPresentationEnlargement U.ι ⊥ X) (normalizedPresentationRestriction U.ι ⊥ X)
    (ParameterTensorNormalizedRowPresentation.forget U.ι X) (restriction U.ι X)
    (normalizedPresentationNull U.ι ⊥ X) (basicNull Q U X)
    (basicSourceIso Q U X).hom
    (ParameterTensorNormalizedRowPresentation.forget (⊥ : Q.Opens).ι X)
    (ParameterTensorNormalizedRowPresentation.forget (inverseOpen U.ι ⊥).ι X)
    ((enlargement_forget U.ι ⊥ X).trans (basicSourceIso_forget Q U X).symm)
    (restriction_forget U.ι ⊥ X).symm (basicNull_comparison Q U X)

/-- Actual empty-support equivalences detect the same basic localization lift. -/
theorem auxiliary_basic_lift_stable_iff :
    IsStableEquivalence
        (ParameterAuxiliaryNormalizedRowLocalization.normalizedPresentationLift U.ι ⊥ X) ↔
      IsStableEquivalence (basicLift Q U X) := by
  have : IsEmpty (inverseOpen U.ι (⊥ : Q.Opens)).toScheme := by
    rw [inverseOpen_bottom]
    infer_instance
  exact homotopyFiberLift_isStableEquivalence_iff
    (normalizedPresentationEnlargement U.ι ⊥ X) (normalizedPresentationRestriction U.ι ⊥ X)
    (ParameterTensorNormalizedRowPresentation.forget U.ι X) (restriction U.ι X)
    (normalizedPresentationNull U.ι ⊥ X) (basicNull Q U X)
    (basicSourceIso Q U X).hom
    (ParameterTensorNormalizedRowPresentation.forget (⊥ : Q.Opens).ι X)
    (ParameterTensorNormalizedRowPresentation.forget (inverseOpen U.ι ⊥).ι X)
    ((enlargement_forget U.ι ⊥ X).trans (basicSourceIso_forget Q U X).symm)
    (restriction_forget U.ι ⊥ X).symm (basicNull_comparison Q U X)
    (fun d => by infer_instance)
    (ParameterTensorNormalizedRowPresentation.bottom_forget_stable Q X)
    (ParameterTensorNormalizedRowPresentation.forget_stable_of_isEmpty _ X)

/-- The actual basic normalized lift is stable under the original qcqs and compact-open hypotheses.
-/
theorem basicLift_integer_isStableEquivalence
    [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U] :
    IsStableEquivalence (basicLift Q U (op integerBase)) :=
  (auxiliary_basic_lift_stable_iff Q U (op integerBase)).mp
    (normalizedPresentationLift_integer_isStableEquivalence
      U.ι ⊥)

/-- Its boundary is defined from the actual basic fiber lift in each original signed degree. -/
def basicConnecting [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U] (d : ℤ) :
    stableHomotopyGroup (ParameterTensorNormalizedRowPresentation.ambient U.toScheme
      (op integerBase)) (d + 1) ⟶
    stableHomotopyGroup (ParameterTensorNormalizedRowPresentation.supported U.ι
      (op integerBase)) d := by
  have : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift (restriction U.ι (op integerBase))
        (ParameterTensorNormalizedRowPresentation.forget U.ι (op integerBase))
        (basicNull Q U (op integerBase)))) :=
    basicLift_integer_isStableEquivalence Q U d
  exact stableFiberLiftConnecting
    (ParameterTensorNormalizedRowPresentation.forget U.ι (op integerBase))
    (restriction U.ι (op integerBase)) (basicNull Q U (op integerBase)) d

/-- The intrinsic basic signed boundary retains the original auxiliary null and source cast. -/
theorem auxiliary_basic_connecting [CompactSpace Q] [QuasiSeparatedSpace Q]
    [CompactSpace U] (d : ℤ) :
    letI : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift (normalizedPresentationRestriction U.ι ⊥ (op integerBase))
        (normalizedPresentationEnlargement U.ι ⊥ (op integerBase))
        (normalizedPresentationNull U.ι ⊥ (op integerBase)))) :=
        normalizedPresentationLift_integer_isStableEquivalence U.ι ⊥ d;
    stableFiberLiftConnecting
        (normalizedPresentationEnlargement U.ι ⊥ (op integerBase))
        (normalizedPresentationRestriction U.ι ⊥ (op integerBase))
        (normalizedPresentationNull U.ι ⊥ (op integerBase)) d ≫
      (stableHomotopyFunctor d).map (basicSourceIso Q U (op integerBase)).hom =
    (stableHomotopyFunctor (d + 1)).map
        (ParameterTensorNormalizedRowPresentation.forget (inverseOpen U.ι ⊥).ι
          (op integerBase)) ≫ basicConnecting Q U d := by
  have : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift (normalizedPresentationRestriction U.ι ⊥ (op integerBase))
        (normalizedPresentationEnlargement U.ι ⊥ (op integerBase))
        (normalizedPresentationNull U.ι ⊥ (op integerBase)))) :=
    normalizedPresentationLift_integer_isStableEquivalence U.ι ⊥ d
  have : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift (restriction U.ι (op integerBase))
        (ParameterTensorNormalizedRowPresentation.forget U.ι (op integerBase))
        (basicNull Q U (op integerBase)))) :=
    basicLift_integer_isStableEquivalence Q U d
  exact stableFiberLiftConnecting_naturality
    (normalizedPresentationEnlargement U.ι ⊥ (op integerBase))
    (normalizedPresentationRestriction U.ι ⊥ (op integerBase))
    (ParameterTensorNormalizedRowPresentation.forget U.ι (op integerBase))
    (restriction U.ι (op integerBase))
    (normalizedPresentationNull U.ι ⊥ (op integerBase)) (basicNull Q U (op integerBase))
    (basicSourceIso Q U (op integerBase)).hom
    (ParameterTensorNormalizedRowPresentation.forget (⊥ : Q.Opens).ι (op integerBase))
    (ParameterTensorNormalizedRowPresentation.forget (inverseOpen U.ι ⊥).ι (op integerBase))
    ((enlargement_forget U.ι ⊥ (op integerBase)).trans
      (basicSourceIso_forget Q U (op integerBase)).symm)
    (restriction_forget U.ι ⊥ (op integerBase)).symm
    (basicNull_comparison Q U (op integerBase)) d

end Quillen.PerfectComplexes.ParameterNormalizedBasicLocalization
