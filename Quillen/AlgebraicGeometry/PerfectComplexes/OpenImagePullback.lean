/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.GrothendieckPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGrothendieckImage

/-!
# Arbitrary quasi-compact open-square action on the original image quotient

The original derived pullback square acts on the fine restriction images.
The proved equality of fine and relative-open images then gives a literal
quotient descent into the unchanged relative-open image quotient. No exact
raw pullback functor or flatness hypothesis is substituted.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.AlgebraicGrothendieck
universe u
namespace Quillen.PerfectComplexes
variable {U X U' X' : Scheme.{u}} [hU : CompactSpace U] [hX : CompactSpace X]
  [hU' : CompactSpace U'] [hX' : CompactSpace X']
  (j : U ⟶ X) (j' : U' ⟶ X') [IsOpenImmersion j] [IsOpenImmersion j']
  (p : X' ⟶ X) (q : U' ⟶ U) (h : q ≫ j = j' ≫ p)

include h in
/-- The original derived group maps commute with the unchanged fine restriction maps. -/
theorem perfectGrothendieckPullback_restrictionSquare :
    (perfectGrothendieckPullback q).comp
      (map (perfectWaldhausen X) (perfectRestrict j) (perfectRestrict_waldhausenExact j)) =
    (map (perfectWaldhausen X') (perfectRestrict j') (perfectRestrict_waldhausenExact j')).comp
      (perfectGrothendieckPullback p) := by
  rw [← perfectGrothendieckPullback_restrict j, ← perfectGrothendieckPullback_restrict j',
    ← perfectGrothendieckPullback_comp, ← perfectGrothendieckPullback_comp, h]

include hX hX' h in
/-- The actual coarse-source image is preserved, via its proved equality with the fine image. -/
theorem perfectOpenImagePullback_range_le :
    (map (perfectOpenWeakWaldhausen j) (perfectRestrict j)
      (perfectOpenRestrict_waldhausenExact j)).range ≤
    (map (perfectOpenWeakWaldhausen j') (perfectRestrict j')
      (perfectOpenRestrict_waldhausenExact j')).range.comap (perfectGrothendieckPullback q) := by
  intro x hx
  rw [range_perfectOpenGrothendieckRestrict j] at hx
  change perfectGrothendieckPullback q x ∈
    (map (perfectOpenWeakWaldhausen j') (perfectRestrict j')
      (perfectOpenRestrict_waldhausenExact j')).range
  rw [range_perfectOpenGrothendieckRestrict j']
  obtain ⟨a, rfl⟩ := hx
  exact ⟨perfectGrothendieckPullback p a,
    (DFunLike.congr_fun (perfectGrothendieckPullback_restrictionSquare j j' p q h) a).symm⟩

/-- The coefficient map descends directly to the unchanged original relative-open quotient. -/
def perfectOpenImageQuotientPullback :
    ImageQuotient (perfectOpenWeakWaldhausen j) (perfectRestrict j)
        (perfectOpenRestrict_waldhausenExact j) →+
    ImageQuotient (perfectOpenWeakWaldhausen j') (perfectRestrict j')
        (perfectOpenRestrict_waldhausenExact j') :=
  QuotientAddGroup.map
    (map (perfectOpenWeakWaldhausen j) (perfectRestrict j)
      (perfectOpenRestrict_waldhausenExact j)).range
    (map (perfectOpenWeakWaldhausen j') (perfectRestrict j')
      (perfectOpenRestrict_waldhausenExact j')).range
    (perfectGrothendieckPullback q) (perfectOpenImagePullback_range_le j j' p q h)

/-- Every original target quotient class is sent by the literal original derived group map. -/
theorem perfectOpenImageQuotientPullback_mk (x : Group (perfectWaldhausen U)) :
    perfectOpenImageQuotientPullback j j' p q h
      (QuotientAddGroup.mk' (map (perfectOpenWeakWaldhausen j) (perfectRestrict j)
        (perfectOpenRestrict_waldhausenExact j)).range x) =
    QuotientAddGroup.mk' (map (perfectOpenWeakWaldhausen j') (perfectRestrict j')
      (perfectOpenRestrict_waldhausenExact j')).range (perfectGrothendieckPullback q x) := rfl

/-- Original bounded-flat classes retain the actual geometric pullback representative. -/
theorem perfectOpenImageQuotientPullback_boundedFlat_objectClass (K : BoundedFlatPerfect U) :
    perfectOpenImageQuotientPullback j j' p q h
      ((imageQuotientGrading (perfectOpenWeakWaldhausen j) (perfectRestrict j)
        (perfectOpenRestrict_waldhausenExact j)).value ((boundedFlatPerfectInclusion U).obj K)) =
    (imageQuotientGrading (perfectOpenWeakWaldhausen j') (perfectRestrict j')
      (perfectOpenRestrict_waldhausenExact j')).value
        ((boundedFlatPerfectInclusion U').obj ((boundedFlatPerfectPullback q).obj K)) := by
  change perfectOpenImageQuotientPullback j j' p q h
    (QuotientAddGroup.mk' (map (perfectOpenWeakWaldhausen j) (perfectRestrict j)
      (perfectOpenRestrict_waldhausenExact j)).range
        (objectClass (perfectWaldhausen U) ((boundedFlatPerfectInclusion U).obj K))) = _
  rw [perfectOpenImageQuotientPullback_mk, perfectGrothendieckPullback_boundedFlat_objectClass]
  rfl

end Quillen.PerfectComplexes
