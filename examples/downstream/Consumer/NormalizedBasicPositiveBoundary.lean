/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedBasicPositiveBoundary

/-!
The intrinsic normalized basic boundary retains original finite K-one classes,
the original supported K-zero endpoint, and the absolute geometric kernel.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.PerfectComplexes ParameterNormalizedBasicLocalization GlobalSectionChangeIndex
open Quillen.PerfectComplexes.Bass Quillen.PerfectComplexes.Bass.SupportedLocalization
universe u
attribute [local instance] basicOver_compactSpace basicOver_quasiSeparatedSpace
attribute [local instance] basicOriginalPair_source_compact basicOriginalPair_target_quasiSeparated
attribute [local instance] basicIdentityPair_source_compact basicIdentityPair_target_quasiSeparated

namespace Consumer.NormalizedBasicPositiveBoundary
variable (Q : Scheme.{u}) (U : Q.Opens)
  [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U]

/-- The absolute original ambient restriction lies in the kernel of the intrinsic basic boundary. -/
theorem basicBoundary_originalAmbientRestriction_eq_zero
    (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : PerfectK Q (n + 1)) :
    basicConnecting Q U (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup
          (ParameterTensorNormalizedRowPresentation.ambient U.toScheme
            (specUnder.obj identityCoefficient))) κ)
        ((normalizedFineAmbientComparison (Over.mk (toIntegerBase U.toScheme)) identityCoefficient
          ((n + 1 : ℕ) : ℤ)).inv
          ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
            ((boundedFlatCoefficientFullOpenBassTelescopeInclusion
              (basicOverInclusion Q U) 0).app identityCoefficient)
            (boundedFlatCoefficientSectionPerfectKStableEquiv
              (op (Over.mk (toIntegerBase U.toScheme)), identityCoefficient) (n + 1)
              (Additive.ofMul (perfectKPullback (identityPairIso
                (basicOriginalPair Q U)).hom.hom.hom.left (n + 1) (perfectKRestrict U.ι
                (n + 1) x))))))) = 0 := by
  have hm : perfectKRestrict U.ι (n + 1) x ∈ (perfectKRestrict U.ι (n + 1)).range :=
    ⟨x, rfl⟩
  rw [range_qcqs_perfectKRestrict_eq_ker_qcqsPerfectConnectingHom U.ι n] at hm
  have hz : qcqsPerfectConnectingHom U.ι n (perfectKRestrict U.ι (n + 1) x) = 1 := hm
  have h := basicConnecting_originalPerfectClass_sign Q U n κ
    (perfectKRestrict U.ι (n + 1) x)
  rw [hz, map_one, ofMul_one, map_zero, map_zero, neg_zero] at h
  exact (ConcreteCategory.bijective_of_isIso
    (normalizedFineSupportComparison (basicOverInclusion Q U) identityCoefficient
      (n : ℤ)).hom).injective (h.trans (map_zero _).symm)

end Consumer.NormalizedBasicPositiveBoundary
