/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryNormalizedRowBoundaryComparison

/-! The actual normalized row keeps its own boundary and arbitrary original negative classes. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
open Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
open Quillen.PerfectComplexes.ParameterAuxiliaryNormalizedRowLocalization
universe u
/-- Degree zero uses only the original ambient compactness hypothesis. -/
example {Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    [CompactSpace Q.left] (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (x : ((ambient T).obj (specUnder.obj a)).waldhausen.K 0) :
    (normalizedFineAmbientComparison T a 0).hom
      (Quillen.KTheory.Bass.SchemeModelRowSeed.normalizedModelClass (ambient T)
        (ParameterLaurentTrack.supportedUnit T.ι)
        (ParameterLaurentTrack.supportedUnit_naturality T.ι) (specUnder.obj a) 0 x) =
      (stableHomotopyFunctor 0).map
        ((boundedFlatCoefficientSupportedAmbientBassTelescopeInclusion T 0).app a)
        (auxiliaryAmbientPerfectStableEquiv T a 0 (Additive.ofMul
          (auxiliaryAmbientPerfectKEquiv T a 0
            (Quillen.Waldhausen.KMap ((ambientComparison Q T).app a).exact 0 x)))) :=
  normalized_fine_ambient_perfectClass T a 0 x

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

/-- The defined row boundary recovers its own original signed fiber boundary through its lift. -/
example (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    normalizedPresentationConnecting f T a d ≫ (stableHomotopyFunctor d).map
        (normalizedPresentationLift f.left T (specUnder.obj a)) =
      stableFiberConnecting (normalizedPresentationRestriction f.left T (specUnder.obj a)) d := by
  have : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift
        (normalizedPresentationRestriction f.left T (specUnder.obj a))
        (normalizedPresentationEnlargement f.left T (specUnder.obj a))
        (normalizedPresentationNull f.left T (specUnder.obj a)))) :=
    normalizedPresentationLift_spec_isStableEquivalence f T a d
  exact stableFiberLiftConnecting_comp_lift _ _ _ d

