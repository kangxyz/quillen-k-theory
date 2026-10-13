/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionKComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionGradingLift
public import Quillen.Waldhausen.Cofinality.GeneralKZeroValue

/-!
# The original full-open section K-zero value and change of weakness

The genuine section joint data supplies the fine small-model factorization used by the
original coarse value map. The accepted algebraic grading lift and the actual evaluation
K-equivalence identify its composite with the unchanged change-of-weak-equivalences map as
the original raw-perfect quotient. Surjectivity follows from target evaluation and quotient
surjectivity, without any assertion that full-open restriction is surjective on K-zero.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.AlgebraicGrothendieck
open Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original coarse section value map lands in the unchanged raw-perfect image quotient. -/
def boundedFlatAffineFullOpenSectionKZeroValueMap (a : Under R) :
    (boundedFlatAffineFullOpenSectionGrading j a).coarseStructure.K 0 →*
      Multiplicative
        (ImageQuotient (perfectOpenWeakWaldhausen (inclusion j a))
          (perfectRestrict (inclusion j a))
          (perfectOpenRestrict_waldhausenExact (inclusion j a))) :=
  (boundedFlatAffineFullOpenSectionGrading j a).coarseKZeroValueMap
    (boundedFlatAffineFullOpenSectionJointData j a).reflexiveSmallModel.sourceFactorization

/-- The genuine original coarse value map detects equality of unchanged coarse section classes. -/
theorem boundedFlatAffineFullOpenSectionKZeroValueMap_injective (a : Under R) :
    Function.Injective (boundedFlatAffineFullOpenSectionKZeroValueMap j a) :=
  (boundedFlatAffineFullOpenSectionGrading j a).coarseKZeroValueMap_injective
    (boundedFlatAffineFullOpenSectionJointData j a).reflexiveSmallModel.sourceFactorization

variable [CompactSpace U]

/-- Actual perfect evaluation commutes with the original inverse algebraic K-zero comparison. -/
theorem boundedFlatAffineFullOpenSectionPerfectKEquiv_grothendieck (a : Under R) :
    (grothendieckKZeroEquivOfSmallModel (perfectWaldhausen (openSpace j a))).symm.toMonoidHom.comp
        (boundedFlatAffineFullOpenSectionPerfectKEquiv j a 0).toMonoidHom =
      (AlgebraicGrothendieck.map (boundedFlatAffineFullOpenSectionWaldhausen j a)
          (boundedFlatAffineFullOpenPerfectEvaluation j a)
          (boundedFlatAffineFullOpenPerfectEvaluation_exact j a)).toMultiplicative.comp
        (grothendieckKZeroEquivOfSmallModel
          (boundedFlatAffineFullOpenSectionWaldhausen j a)).symm.toMonoidHom := by
  apply kZero_hom_ext (boundedFlatAffineFullOpenSectionWaldhausen j a)
  intro S
  change (grothendieckKZeroEquivOfSmallModel (perfectWaldhausen (openSpace j a))).symm
      (boundedFlatAffineFullOpenSectionPerfectKEquiv j a 0
        ((boundedFlatAffineFullOpenSectionWaldhausen j a).kZeroObjectClass S)) =
    (AlgebraicGrothendieck.map (boundedFlatAffineFullOpenSectionWaldhausen j a)
      (boundedFlatAffineFullOpenPerfectEvaluation j a)
      (boundedFlatAffineFullOpenPerfectEvaluation_exact j a)).toMultiplicative
        ((grothendieckKZeroEquivOfSmallModel
          (boundedFlatAffineFullOpenSectionWaldhausen j a)).symm
            ((boundedFlatAffineFullOpenSectionWaldhausen j a).kZeroObjectClass S))
  rw [boundedFlatAffineFullOpenSectionPerfectKEquiv_objectClass,
    grothendieckKZeroEquivOfSmallModel_symm_objectClass,
    grothendieckKZeroEquivOfSmallModel_symm_objectClass]
  exact congrArg Multiplicative.ofAdd
    (map_objectClass (boundedFlatAffineFullOpenSectionWaldhausen j a)
      (boundedFlatAffineFullOpenPerfectEvaluation j a)
      (boundedFlatAffineFullOpenPerfectEvaluation_exact j a) S).symm

/-- The original changeWeak value is the original raw quotient after the actual evaluation. -/
theorem boundedFlatAffineFullOpenSectionKZeroValueMap_comp_changeWeak (a : Under R) :
    (boundedFlatAffineFullOpenSectionKZeroValueMap j a).comp
        (KMap (Fibration.changeWeak_exact (boundedFlatAffineFullOpenSectionGrading j a).nested) 0) =
      (QuotientAddGroup.mk'
        (AlgebraicGrothendieck.map (perfectOpenWeakWaldhausen (inclusion j a))
          (perfectRestrict (inclusion j a))
          (perfectOpenRestrict_waldhausenExact (inclusion j a))).range).toMultiplicative.comp
        ((grothendieckKZeroEquivOfSmallModel
          (perfectWaldhausen (openSpace j a))).symm.toMonoidHom.comp
            (boundedFlatAffineFullOpenSectionPerfectKEquiv j a 0).toMonoidHom) := by
  change ((boundedFlatAffineFullOpenSectionGrading j a).coarseKZeroValueMap
    (boundedFlatAffineFullOpenSectionJointData j a).reflexiveSmallModel.sourceFactorization).comp
      _ = _
  rw [Cofinality.Grading.coarseKZeroValueMap_comp_changeWeak,
    boundedFlatAffineFullOpenSectionGrading_lift,
    boundedFlatAffineFullOpenSectionPerfectKEquiv_grothendieck]
  rfl

/-- Every original graded section K-zero class has a preimage under the unchanged changeWeak map. -/
theorem boundedFlatAffineFullOpenSection_changeWeakKMap_zero_surjective (a : Under R) :
    Function.Surjective
      (KMap (Fibration.changeWeak_exact
        (boundedFlatAffineFullOpenSectionGrading j a).nested) 0) := by
  intro y
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk'_surjective
    (AlgebraicGrothendieck.map (perfectOpenWeakWaldhausen (inclusion j a))
      (perfectRestrict (inclusion j a))
      (perfectOpenRestrict_waldhausenExact (inclusion j a))).range
    (boundedFlatAffineFullOpenSectionKZeroValueMap j a y).toAdd
  obtain ⟨x, hx⟩ := (boundedFlatAffineFullOpenSectionPerfectKEquiv j a 0).surjective
    (grothendieckKZeroEquivOfSmallModel (perfectWaldhausen (openSpace j a))
      (Multiplicative.ofAdd z))
  refine ⟨x, boundedFlatAffineFullOpenSectionKZeroValueMap_injective j a ?_⟩
  have he := DFunLike.congr_fun
    (boundedFlatAffineFullOpenSectionKZeroValueMap_comp_changeWeak j a) x
  change boundedFlatAffineFullOpenSectionKZeroValueMap j a
      (KMap (Fibration.changeWeak_exact (boundedFlatAffineFullOpenSectionGrading j a).nested) 0 x) =
    (QuotientAddGroup.mk'
      (AlgebraicGrothendieck.map (perfectOpenWeakWaldhausen (inclusion j a))
        (perfectRestrict (inclusion j a))
        (perfectOpenRestrict_waldhausenExact (inclusion j a))).range).toMultiplicative
      ((grothendieckKZeroEquivOfSmallModel (perfectWaldhausen (openSpace j a))).symm
        (boundedFlatAffineFullOpenSectionPerfectKEquiv j a 0 x)) at he
  rw [hx, MulEquiv.symm_apply_apply] at he
  exact he.trans (congrArg Multiplicative.ofAdd hz)

end Quillen.PerfectComplexes
