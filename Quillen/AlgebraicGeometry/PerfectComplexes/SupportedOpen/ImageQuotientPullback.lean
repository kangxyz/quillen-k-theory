/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.GrothendieckPullback
public import Quillen.Waldhausen.GrothendieckGroup.Image

/-!
# Actual supported restriction-image quotient pullback

The grading is the quotient by the original supported relative restriction's
algebraic image. Its arbitrary pair-square action descends from the proved
original supported Grothendieck restriction square. An actual relative
pullback class supplies each image-preservation witness; no density,
surjectivity, or raw-perfect exact pullback premise is used.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.AlgebraicGrothendieck
universe u
namespace Quillen.PerfectComplexes

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The unchanged raw supported quotient by the actual relative restriction image. -/
abbrev PerfectSupportedOpenImageQuotient :=
  ImageQuotient (perfectSupportedOpenWeakWaldhausen j T) (perfectSupportedRestrict j T)
    (perfectSupportedOpenRestrict_waldhausenExact j T)

/-- Original supported perfect complexes carry their actual relative image-quotient grades. -/
def perfectSupportedOpenDeficitGrading :
    Cofinality.Grading (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι)
      (PerfectSupportedOpenImageQuotient j T) :=
  imageQuotientGrading (perfectSupportedOpenWeakWaldhausen j T) (perfectSupportedRestrict j T)
    (perfectSupportedOpenRestrict_waldhausenExact j T)

/-- The actual supported quotient grade detects exactly the original algebraic image. -/
theorem perfectSupportedOpenDeficitGrading_zero_iff
    (K : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory) :
    (perfectSupportedOpenDeficitGrading j T).value K = 0 ↔
      objectClass (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) K ∈
        (map (perfectSupportedOpenWeakWaldhausen j T) (perfectSupportedRestrict j T)
          (perfectSupportedOpenRestrict_waldhausenExact j T)).range :=
  imageQuotientGrading_zero_iff _ _ _ K

variable {U' X' : Scheme.{u}} (j' : U' ⟶ X') [IsOpenImmersion j'] {S : X'.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.hom.right = g ≫ j)
  [CompactSpace X'] [CompactSpace X] [CompactSpace U'] [CompactSpace U]

/-- Every actual supported relative image class has an original pulled-back relative witness. -/
theorem perfectSupportedOpenImagePullback_range_le :
    (map (perfectSupportedOpenWeakWaldhausen j T) (perfectSupportedRestrict j T)
      (perfectSupportedOpenRestrict_waldhausenExact j T)).range ≤
    (map (perfectSupportedOpenWeakWaldhausen j' S) (perfectSupportedRestrict j' S)
      (perfectSupportedOpenRestrict_waldhausenExact j' S)).range.comap
        (perfectSupportedGrothendieckPullback
          (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w))) := by
  rintro x ⟨a, rfl⟩
  exact ⟨perfectSupportedOpenGrothendieckPullback j' j f g w a,
    (DFunLike.congr_fun
      (perfectSupportedOpenGrothendieckPullback_restrictionSquare j' j f g w) a).symm⟩

/-- Actual arbitrary supported pair squares act on the unchanged raw restriction-image quotient. -/
def perfectSupportedOpenImageQuotientPullback :
    PerfectSupportedOpenImageQuotient j T →+ PerfectSupportedOpenImageQuotient j' S := by
  let φ : Group (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) →+
      Group (perfectSupportedWaldhausen (j' ⁻¹ᵁ S).ι) := by
    simpa (config := { instances := true }) only
      [qcSupportedBaseSquare, supportedPairTargetSquare, supportOpenPair, Arrow.mk] using
      (perfectSupportedGrothendieckPullback
        (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w)))
  have hφ : (map (perfectSupportedOpenWeakWaldhausen j T) (perfectSupportedRestrict j T)
      (perfectSupportedOpenRestrict_waldhausenExact j T)).range ≤
    (map (perfectSupportedOpenWeakWaldhausen j' S) (perfectSupportedRestrict j' S)
      (perfectSupportedOpenRestrict_waldhausenExact j' S)).range.comap φ := by
    simpa (config := { instances := true }) only
      [φ, qcSupportedBaseSquare, supportedPairTargetSquare, supportOpenPair, Arrow.mk] using
      (perfectSupportedOpenImagePullback_range_le j T j' f g w)
  exact QuotientAddGroup.map
    (G := Group (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι))
    (H := Group (perfectSupportedWaldhausen (j' ⁻¹ᵁ S).ι))
    (map (perfectSupportedOpenWeakWaldhausen j T) (perfectSupportedRestrict j T)
      (perfectSupportedOpenRestrict_waldhausenExact j T)).range
    (map (perfectSupportedOpenWeakWaldhausen j' S) (perfectSupportedRestrict j' S)
      (perfectSupportedOpenRestrict_waldhausenExact j' S)).range
    φ hφ

/-- Every original quotient class is sent by the literal supported Grothendieck pullback. -/
theorem perfectSupportedOpenImageQuotientPullback_mk
    (x : Group (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι)) :
    perfectSupportedOpenImageQuotientPullback j T j' f g w
      (QuotientAddGroup.mk' (map (perfectSupportedOpenWeakWaldhausen j T)
        (perfectSupportedRestrict j T) (perfectSupportedOpenRestrict_waldhausenExact j T)).range
        x) =
    QuotientAddGroup.mk' (map (perfectSupportedOpenWeakWaldhausen j' S)
      (perfectSupportedRestrict j' S) (perfectSupportedOpenRestrict_waldhausenExact j' S)).range
      (perfectSupportedGrothendieckPullback
        (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w)) x) := rfl

/-- Bounded-flat supported quotient representatives retain their actual open-side pair pullback. -/
theorem perfectSupportedOpenImageQuotientPullback_boundedFlat_objectClass
    (K : (boundedFlatPerfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory) :
    perfectSupportedOpenImageQuotientPullback j T j' f g w
      ((perfectSupportedOpenDeficitGrading j T).value
        ((boundedFlatPerfectSupportedInclusion (j ⁻¹ᵁ T).ι).obj K)) =
    (perfectSupportedOpenDeficitGrading j' S).value
      ((boundedFlatPerfectSupportedInclusion (j' ⁻¹ᵁ S).ι).obj
        ((boundedFlatPerfectSupportedPullback (supportedPairTargetSquare j' j f g w)).obj K)) := by
  change perfectSupportedOpenImageQuotientPullback j T j' f g w
      (QuotientAddGroup.mk' (map (perfectSupportedOpenWeakWaldhausen j T)
        (perfectSupportedRestrict j T) (perfectSupportedOpenRestrict_waldhausenExact j T)).range
        (objectClass (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι)
          ((boundedFlatPerfectSupportedInclusion (j ⁻¹ᵁ T).ι).obj K))) = _
  rw [perfectSupportedOpenImageQuotientPullback_mk]
  have h := perfectSupportedGrothendieckPullback_boundedFlat_objectClass
    (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w)) K
  simp (config := { instances := true }) only
    [qcSupportedBaseSquare, supportedPairTargetSquare, supportOpenPair, Arrow.mk] at h
  exact congrArg (QuotientAddGroup.mk'
    (map (perfectSupportedOpenWeakWaldhausen j' S) (perfectSupportedRestrict j' S)
      (perfectSupportedOpenRestrict_waldhausenExact j' S)).range) h

end Quillen.PerfectComplexes
