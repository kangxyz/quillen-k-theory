/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryNegativeBoundarySign

/-! Regression properties of the unchanged auxiliary original negative classes and boundary. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.KTheory.Bass.SchemeNaturalSeed Quillen.PerfectComplexes
open GlobalSectionChangeIndex ParameterAuxiliarySupport GlobalAuxiliaryParameterCoefficient
open ParameterAuxiliaryCurrentFiber
universe u
namespace QuillenTest

attribute [local instance] supportObject_compactSpace
  fiberNegativeFineClass_isIso openNegativeFineClass_isIso

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

omit [IsOpenImmersion f.left] [CompactSpace Q.left] in
/-- The inverse-image open is compact from the original hypotheses alone. -/
theorem auxiliaryInverseOpen_compact : CompactSpace (inverseOpen f.left T) :=
  inverseOpen_compactSpace f T

/-- Every original union-support negative class survives the actual fine class map. -/
theorem auxiliaryFiberNegativeFineClass_roundtrip (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (x : (Quillen.PerfectComplexes.Bass.supportedNegativeKFunctor i).obj
      ((boundedFlatCoefficientQuasiCompactOpenPairRow
        (supportArrow Q (unionOpen f.left T))).obj a)) :
    inv (fiberNegativeFineClass f T i a) (fiberNegativeFineClass f T i a x) = x := by
  rw [← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]

/-- At all later negative indices the intrinsic boundary on an original class agrees with
its original fine cone value and the unchanged degree cast. -/
theorem auxiliaryNegativeBoundary_originalClass (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (x : (Quillen.PerfectComplexes.Bass.supportedNegativeKFunctor (i + 2)).obj
      ((boundedFlatCoefficientQuasiCompactOpenPairRow
        (supportArrow P (inverseOpen f.left T))).obj a)) :
    letI : CompactSpace (inverseOpen f.left T) := inverseOpen_compactSpace f T;
    letI : QuasiSeparatedSpace P.left := open_quasiSeparatedSpace f;
    (currentFineSupportComparison f T a (-((i + 2 + 1 : ℕ) : ℤ))).hom
      (currentConnecting f T a (-((i + 2 + 1 : ℕ) : ℤ))
        ((negativeLocalizationDegreeIso (i + 2)).hom.app
          ((currentTelescope (openAction f.left T)).obj (specUnder.obj a))
          ((GlobalSupportedParameterCoefficient.currentNegativeKComparison
            (supportArrow P (inverseOpen f.left T)) (i + 2)).hom.app a x))) =
    boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a (-((i + 2 + 1 : ℕ) : ℤ))
      ((negativeLocalizationDegreeIso (i + 2)).hom.app
        ((boundedFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T).obj a)
        (openNegativeFineClass f T (i + 2) a x)) := by
  let : CompactSpace (inverseOpen f.left T) := inverseOpen_compactSpace f T
  let : QuasiSeparatedSpace P.left := open_quasiSeparatedSpace f
  exact congrArg (fun k => k x) (currentNegativeConnecting_fine f T (i + 2) a)

end QuillenTest
