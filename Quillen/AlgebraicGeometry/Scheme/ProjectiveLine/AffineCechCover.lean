/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Charts

/-!
# Affine intersections in the original projective-line cover

The two original polynomial charts form a cover whose every nonempty intersection
is affine. The mixed intersection is identified with the original Laurent scheme,
including compatibility with its map to the projective line. In particular, every
intersection indexed by a simplex of the usual Cech object is affine.

These are geometric prerequisites for an affine-cover cohomology computation.
No Cech-to-derived comparison or projective bundle formula is asserted. The base
is an arbitrary commutative ring, including the zero ring.
-/
@[expose] public section
open Quillen


noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u v
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent
variable (R : CommRingCat.{u})

/-- The two original chart opens; `true` is the positive polynomial chart. -/
def chartOpen (b : Bool) : (twoChartLine R).Opens :=
  if b then (plusChart R).opensRange else (minusChart R).opensRange

@[simp] lemma chartOpen_true : chartOpen R true = (plusChart R).opensRange := rfl
@[simp] lemma chartOpen_false : chartOpen R false = (minusChart R).opensRange := rfl

lemma chartOpen_isOpenCover : IsOpenCover (chartOpen R) := by
  simpa only [IsOpenCover, iSup_bool_eq, chartOpen_false, chartOpen_true, sup_comm]
    using chart_ranges_cover R

lemma isAffineOpen_chartOpen (b : Bool) : IsAffineOpen (chartOpen R b) := by
  cases b <;> exact isAffineOpen_opensRange _

lemma isAffineOpen_chartOpen_inter :
    IsAffineOpen (chartOpen R true ⊓ chartOpen R false) := by
  rw [chartOpen_true, chartOpen_false, chart_ranges_inter]
  exact isAffineOpen_opensRange _

/-- The actual mixed chart intersection is the original Laurent affine scheme. -/
def overlapIso : Spec (.of (LaurentPolynomial R)) ≅
    ((plusChart R).opensRange ⊓ (minusChart R).opensRange).toScheme :=
  IsOpenImmersion.isoOfRangeEq (laurentPlus R ≫ plusChart R)
    ((plusChart R).opensRange ⊓ (minusChart R).opensRange).ι (by
      change ((laurentPlus R ≫ plusChart R).opensRange : Set (twoChartLine R)) = _
      rw [← chart_ranges_inter]
      exact Subtype.range_coe.symm)

@[reassoc (attr := simp)] lemma overlapIso_hom_ι :
    (overlapIso R).hom ≫ ((plusChart R).opensRange ⊓ (minusChart R).opensRange).ι =
      laurentPlus R ≫ plusChart R :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- An intersection containing both chart indices is precisely the Laurent open. -/
lemma iInf_chartOpen_of_mixed {ι : Sort v} (a : ι → Bool)
    (hp : ∃ i, a i = true) (hm : ∃ i, a i = false) :
    (⨅ i, chartOpen R (a i)) = chartOpen R true ⊓ chartOpen R false := by
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hm
  apply le_antisymm
  · exact le_inf (hi ▸ iInf_le (fun k => chartOpen R (a k)) i)
      (hj ▸ iInf_le (fun k => chartOpen R (a k)) j)
  · apply le_iInf
    intro k
    cases a k
    · exact inf_le_right
    · exact inf_le_left

/-- Every nonempty intersection of members of the original two-chart cover is
an affine open. No finiteness assumption on the indexing type is necessary. -/
theorem isAffineOpen_iInf_chartOpen {ι : Sort v} [Nonempty ι] (a : ι → Bool) :
    IsAffineOpen (⨅ i, chartOpen R (a i)) := by
  classical
  by_cases hp : ∃ i, a i = true
  · by_cases hm : ∃ i, a i = false
    · rw [iInf_chartOpen_of_mixed R a hp hm]
      exact isAffineOpen_chartOpen_inter R
    · have h (i) : a i = true := by
        cases h : a i
        · exact False.elim (hm ⟨i, h⟩)
        · rfl
      simpa only [h, iInf_const] using isAffineOpen_chartOpen R true
  · have h (i) : a i = false := by
      cases h : a i
      · rfl
      · exact False.elim (hp ⟨i, h⟩)
    simpa only [h, iInf_const] using isAffineOpen_chartOpen R false

/-- Every geometric intersection used in the ordinary Cech cosimplicial object
of the two original charts is affine, in every cosimplicial degree. -/
theorem isAffineOpen_cechIntersection (n : ℕ) (a : Fin (n + 1) → Bool) :
    IsAffineOpen (∏ᶜ fun i => chartOpen R (a i)) := by
  have h : (∏ᶜ fun i => chartOpen R (a i)) = ⨅ i, chartOpen R (a i) := by
    apply le_antisymm
    · exact le_iInf fun i => leOfHom (Limits.Pi.π _ i)
    · exact leOfHom (Limits.Pi.lift fun i => homOfLE (iInf_le _ i))
  rw [h]
  exact isAffineOpen_iInf_chartOpen R a

end AlgebraicGeometry.Scheme.ProjectiveLine
