/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionJointData
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.KComparison
public import Quillen.AlgebraicGeometry.Scheme.Affine.OpenPairCompactness
public import Quillen.Waldhausen.Functoriality.ExactEquivalence
public import Quillen.Waldhausen.GrothendieckComparison.SmallModel

/-!
# Original full-open section evaluation on K-groups

The actual full-open evaluation equivalence is lifted through `AsSmall` to match the section
hom universe. Exactness in both directions gives the original all-degree bounded-flat
K-equivalence, then the original bounded-flat inclusion computes perfect K-theory on the
compact open fiber. The comparison retains the exact original object-loop classes, without
identifying the section Model with its small model or normalizing the evaluation's image zero.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Original full-open evaluation followed by the existing common-universe equivalence. -/
def boundedFlatAffineFullOpenSectionSmallEquivalence (a : Under R) :
    BoundedFlatAffineFullOpenSections j a ≌ SmallModel (BoundedFlatPerfect (openSpace j a)) :=
  (boundedFlatAffineFullOpenSectionEquivalence j a).trans AsSmall.equiv

/-- The actual lifted evaluation preserves the original full-open Waldhausen classes. -/
theorem boundedFlatAffineFullOpenSectionSmallEquivalence_exact (a : Under R) :
    IsExact (boundedFlatAffineFullOpenSectionWaldhausen j a).cof
      (boundedFlatAffineFullOpenSectionWaldhausen j a).weq
      (boundedFlatPerfectWaldhausen (openSpace j a)).smallModel.cof
      (boundedFlatPerfectWaldhausen (openSpace j a)).smallModel.weq
      (boundedFlatAffineFullOpenSectionSmallEquivalence j a).functor :=
  (boundedFlatAffineFullOpenOriginalEvaluation_exact j a).comp
    (boundedFlatPerfectWaldhausen (openSpace j a)).smallModel_up_exact

/-- The original inverse lowers the universe before applying the exact evaluation inverse. -/
theorem boundedFlatAffineFullOpenSectionSmallEquivalence_inverse_exact (a : Under R) :
    IsExact (boundedFlatPerfectWaldhausen (openSpace j a)).smallModel.cof
      (boundedFlatPerfectWaldhausen (openSpace j a)).smallModel.weq
      (boundedFlatAffineFullOpenSectionWaldhausen j a).cof
      (boundedFlatAffineFullOpenSectionWaldhausen j a).weq
      (boundedFlatAffineFullOpenSectionSmallEquivalence j a).inverse :=
  (boundedFlatPerfectWaldhausen (openSpace j a)).smallModel_down_exact.comp
    (boundedFlatAffineFullOpenSectionEquivalence_inverse_exact j a)

/-- Actual section evaluation computes every original bounded-flat K-group of the open fiber. -/
def boundedFlatAffineFullOpenSectionKEquiv (a : Under R) (n : ℕ) :
    (boundedFlatAffineFullOpenSectionWaldhausen j a).K n ≃*
      (boundedFlatPerfectWaldhausen (openSpace j a)).K n :=
  (KEquivOfExactEquivalence (boundedFlatAffineFullOpenSectionWaldhausen j a)
    (boundedFlatPerfectWaldhausen (openSpace j a)).smallModel
    (boundedFlatAffineFullOpenSectionSmallEquivalence j a)
    (boundedFlatAffineFullOpenSectionSmallEquivalence_exact j a)
    (boundedFlatAffineFullOpenSectionSmallEquivalence_inverse_exact j a) n).trans
      ((boundedFlatPerfectWaldhausen (openSpace j a)).smallModelKEquiv n).symm

/-- The forward comparison is the original exact evaluation K-map followed by universe lowering. -/
theorem boundedFlatAffineFullOpenSectionKEquiv_apply (a : Under R) (n : ℕ)
    (x : (boundedFlatAffineFullOpenSectionWaldhausen j a).K n) :
    boundedFlatAffineFullOpenSectionKEquiv j a n x =
      ((boundedFlatPerfectWaldhausen (openSpace j a)).smallModelKEquiv n).symm
        (KMap (boundedFlatAffineFullOpenSectionSmallEquivalence_exact j a) n x) := rfl

/-- The actual evaluation comparison retains the original evaluated object's K-zero class. -/
@[simp] theorem boundedFlatAffineFullOpenSectionKEquiv_objectClass (a : Under R)
    (S : BoundedFlatAffineFullOpenSections j a) :
    boundedFlatAffineFullOpenSectionKEquiv j a 0
        ((boundedFlatAffineFullOpenSectionWaldhausen j a).kZeroObjectClass S) =
      (boundedFlatPerfectWaldhausen (openSpace j a)).kZeroObjectClass
        ((boundedFlatAffineFullOpenOriginalEvaluation j a).obj S) := by
  rw [boundedFlatAffineFullOpenSectionKEquiv_apply]
  apply ((boundedFlatPerfectWaldhausen (openSpace j a)).smallModelKEquiv 0).injective
  rw [MulEquiv.apply_symm_apply, Structure.smallModelKEquiv_objectClass]
  exact KMap_kZeroObjectClass (boundedFlatAffineFullOpenSectionSmallEquivalence_exact j a) S

variable [CompactSpace U]

/-- Original full-open section evaluation followed by the original perfect comparison. -/
def boundedFlatAffineFullOpenSectionPerfectKEquiv (a : Under R) (n : ℕ) :
    (boundedFlatAffineFullOpenSectionWaldhausen j a).K n ≃*
      (perfectWaldhausen (openSpace j a)).K n := by
  letI : CompactSpace (openSpace j a) := compactSpace_openSpace j a
  exact (boundedFlatAffineFullOpenSectionKEquiv j a n).trans
    (boundedFlatPerfectKEquiv (openSpace j a) n)

/-- The perfect comparison retains the original bounded-flat inclusion map after evaluation. -/
theorem boundedFlatAffineFullOpenSectionPerfectKEquiv_apply (a : Under R) (n : ℕ)
    (x : (boundedFlatAffineFullOpenSectionWaldhausen j a).K n) :
    boundedFlatAffineFullOpenSectionPerfectKEquiv j a n x =
      boundedFlatPerfectToPerfectKMap (openSpace j a) n
        (boundedFlatAffineFullOpenSectionKEquiv j a n x) := rfl

/-- The original perfect evaluation is retained exactly on every original section object class. -/
@[simp] theorem boundedFlatAffineFullOpenSectionPerfectKEquiv_objectClass (a : Under R)
    (S : BoundedFlatAffineFullOpenSections j a) :
    boundedFlatAffineFullOpenSectionPerfectKEquiv j a 0
        ((boundedFlatAffineFullOpenSectionWaldhausen j a).kZeroObjectClass S) =
      (perfectWaldhausen (openSpace j a)).kZeroObjectClass
        ((boundedFlatAffineFullOpenPerfectEvaluation j a).obj S) := by
  rw [boundedFlatAffineFullOpenSectionPerfectKEquiv_apply,
    boundedFlatAffineFullOpenSectionKEquiv_objectClass]
  exact KMap_kZeroObjectClass (boundedFlatPerfectInclusion_exact (openSpace j a)) _

end Quillen.PerfectComplexes
