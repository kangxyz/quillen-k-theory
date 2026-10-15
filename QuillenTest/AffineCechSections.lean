/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Affine.GlobalSectionsExactness
public import Mathlib.Data.ZMod.Basic

/-!
# Actual affine Cech and global-section consumers

The concrete cover of `Spec (ZMod 6)` has coordinates `2, 3, 0`: it tests
zero divisors and an empty principal open. The cocycle consumer retains the
original sections, restrictions, and coboundary equation. The short-exact
consumers require quasicoherence only of the kernel.
-/
@[expose] public section


noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open PrimeSpectrum AlgebraicGeometry.Scheme.Modules.AffineCech

namespace QuillenTest.AffineCechSections


abbrev torsionRing : CommRingCat := CommRingCat.of (ZMod 6)

lemma torsion_ring_zero_divisors :
    (2 : torsionRing) ≠ 0 ∧ (3 : torsionRing) ≠ 0 ∧
      (2 : torsionRing) * 3 = 0 := by decide

def coverCoordinates : Fin 3 → torsionRing := ![2, 3, 0]

lemma coverCoordinates_cover : (⨆ i, basicOpen (coverCoordinates i)) = ⊤ := by
  apply iSup_basicOpen_eq_top_iff.mpr
  apply (Ideal.eq_top_iff_one _).mpr
  have h2 : (2 : torsionRing) ∈ Ideal.span (Set.range coverCoordinates) :=
    Ideal.subset_span ⟨0, rfl⟩
  have h3 : (3 : torsionRing) ∈ Ideal.span (Set.range coverCoordinates) :=
    Ideal.subset_span ⟨1, rfl⟩
  have h := (Ideal.span (Set.range coverCoordinates)).sub_mem h3 h2
  convert h using 1; decide

lemma coverCoordinates_empty_open : basicOpen (coverCoordinates 2) = ⊥ := by
  change basicOpen (0 : torsionRing) = ⊥
  exact basicOpen_zero

lemma original_cocycle_is_coboundary
    (M : (Spec torsionRing).Modules) [M.IsQuasicoherent]
    (c : ∀ i j, Section M
      (basicOpen (coverCoordinates i) ⊓ basicOpen (coverCoordinates j)))
    (hc : ∀ i j k,
      res M (inf_le_left : (basicOpen (coverCoordinates i) ⊓
        basicOpen (coverCoordinates j)) ⊓ basicOpen (coverCoordinates k) ≤ _) (c i j) +
      res M (inf_le_inf inf_le_right le_rfl) (c j k) =
      res M (inf_le_inf inf_le_left le_rfl) (c i k)) :
    ∃ t : ∀ i, Section M (basicOpen (coverCoordinates i)), ∀ i j,
      res M inf_le_right (t j) - res M inf_le_left (t i) = c i j :=
  exists_cechOne_coboundary M coverCoordinates coverCoordinates_cover c hc

lemma original_global_section_lifts {R : CommRingCat.{u}}
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] (z : (moduleSpecΓFunctor.obj S.X₃)) :
    ∃ t : (moduleSpecΓFunctor.obj S.X₂), (moduleSpecΓFunctor.map S.g) t = z :=
  exists_global_section_lift hS z

lemma original_globalSections_shortExact {R : CommRingCat.{u}}
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] : (S.map moduleSpecΓFunctor).ShortExact :=
  shortExact_globalSections_of_quasicoherent_kernel hS

end QuillenTest.AffineCechSections
