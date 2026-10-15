/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenKZeroImage
public import Quillen.AlgebraicGeometry.PerfectComplexes.GrothendieckComparison
public import Quillen.Waldhausen.GrothendieckGroup.Image

/-!
# The original fine and relative-open algebraic restriction images

The accepted equality of the actual K-zero restriction images transports
through the genuine original Grothendieck comparisons. The resulting equality
is in the unchanged target group of perfect complexes on the open. The explicit
quotient equivalence sends each fine quotient class to the same class in the
original relative-open image quotient; it does not replace that grading.
-/
@[expose] public section

open Quillen.Waldhausen


noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.AlgebraicGrothendieck
universe u v
namespace Quillen.PerfectComplexes

private theorem original_map_mem_range {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : Structure C) (V : Structure D) (F : C ⥤ D)
    (hF : IsExact W.cof W.weq V.cof V.weq F) (y : Group V) :
    y ∈ (map W F hF).range ↔
      grothendieckKZeroEquivOfSmallModel V (Multiplicative.ofAdd y) ∈ (KMap hF 0).range := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨grothendieckKZeroEquivOfSmallModel W (Multiplicative.ofAdd a),
      grothendieckKZeroEquivOfSmallModel_natural W V F hF (Multiplicative.ofAdd a)⟩
  · rintro ⟨a, ha⟩
    refine ⟨((grothendieckKZeroEquivOfSmallModel W).symm a).toAdd, ?_⟩
    have hn := grothendieckKZeroEquivOfSmallModel_natural W V F hF
      ((grothendieckKZeroEquivOfSmallModel W).symm a)
    rw [MulEquiv.apply_symm_apply] at hn
    exact congrArg Multiplicative.toAdd
      ((grothendieckKZeroEquivOfSmallModel V).injective (hn.symm.trans ha))

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual relative-open and fine restriction images coincide in the original target group. -/
theorem range_perfectOpenGrothendieckRestrict :
    (map (perfectOpenWeakWaldhausen j) (perfectRestrict j)
      (perfectOpenRestrict_waldhausenExact j)).range =
    (map (perfectWaldhausen X) (perfectRestrict j) (perfectRestrict_waldhausenExact j)).range := by
  ext y
  rw [original_map_mem_range (perfectOpenWeakWaldhausen j) (perfectWaldhausen U)
    (perfectRestrict j) (perfectOpenRestrict_waldhausenExact j),
    original_map_mem_range (perfectWaldhausen X) (perfectWaldhausen U)
      (perfectRestrict j) (perfectRestrict_waldhausenExact j)]
  change grothendieckKZeroEquivOfSmallModel (perfectWaldhausen U) (Multiplicative.ofAdd y) ∈
      (perfectOpenKRestrict j 0).range ↔
    grothendieckKZeroEquivOfSmallModel (perfectWaldhausen U) (Multiplicative.ofAdd y) ∈
      (perfectKRestrict j 0).range
  rw [range_perfectOpenKRestrict_zero]

/-- The fine image quotient maps canonically to the unchanged original relative-open quotient. -/
def perfectFineOpenImageQuotientEquiv :
    ImageQuotient (perfectWaldhausen X) (perfectRestrict j) (perfectRestrict_waldhausenExact j) ≃+
    ImageQuotient (perfectOpenWeakWaldhausen j) (perfectRestrict j)
      (perfectOpenRestrict_waldhausenExact j) :=
  QuotientAddGroup.quotientAddEquivOfEq (range_perfectOpenGrothendieckRestrict j).symm

/-- Both quotient projections retain the exact same original target algebraic class. -/
theorem perfectFineOpenImageQuotientEquiv_mk (y : Group (perfectWaldhausen U)) :
    perfectFineOpenImageQuotientEquiv j
      (QuotientAddGroup.mk'
        (map (perfectWaldhausen X) (perfectRestrict j)
          (perfectRestrict_waldhausenExact j)).range y) =
    QuotientAddGroup.mk' (map (perfectOpenWeakWaldhausen j) (perfectRestrict j)
      (perfectOpenRestrict_waldhausenExact j)).range y := rfl

/-- The explicit comparison keeps the original relative-open object grading as its target. -/
theorem perfectFineOpenImageQuotientEquiv_objectClass (K : Perfect U) :
    perfectFineOpenImageQuotientEquiv j
      ((imageQuotientGrading (perfectWaldhausen X) (perfectRestrict j)
        (perfectRestrict_waldhausenExact j)).value K) =
    (imageQuotientGrading (perfectOpenWeakWaldhausen j) (perfectRestrict j)
      (perfectOpenRestrict_waldhausenExact j)).value K := rfl

end Quillen.PerfectComplexes
