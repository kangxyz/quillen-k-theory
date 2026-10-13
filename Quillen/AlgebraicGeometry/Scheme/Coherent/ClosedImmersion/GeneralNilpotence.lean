/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.AffineKernel
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.GeneralSupport
public import Quillen.Devissage.KernelIteration

/-!
# Finite ideal-kernel nilpotence on a noetherian scheme

Affine ideal-power exponents, the canonical unit-kernel base-change square,
and an actual finite affine subcover give one terminating exponent for each
supported coherent sheaf. No bound uniform in the sheaf is assumed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.CoherentScheme.ClosedImmersion.General
open ReflectorDevissage

variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- Every genuine unit-kernel iterate commutes with actual open restriction. -/
def kernelIterateOpenBaseChange {V : Scheme.{u}} [IsLocallyNoetherian V]
    (a : V ⟶ X) [IsOpenImmersion a] (n : ℕ) (M : FiniteTypeSheaves X) :
    (finiteTypeSheavesRestriction a).obj (kernelIterate (coherentAdjunction i).unit n M) ≅
      kernelIterate (coherentAdjunction (pullback.snd i a)).unit n
        ((finiteTypeSheavesRestriction a).obj M) := by
  induction n generalizing M with
  | zero => exact Iso.refl _
  | succ n ih =>
    exact ih (kernelStep (coherentAdjunction i).unit M) ≪≫
      kernelIterateIso (coherentAdjunction (pullback.snd i a)).unit n
        (kernelUnitOpenBaseChange i a M)

/-- A closed immersion into an affine scheme has the actual quotient
zero-locus image, with its genuine source isomorphism accounted for. -/
theorem affinePresentation_range {Z : Scheme.{u}}
    (R : CommRingCat.{u})
    (i : Z ⟶ Spec R)
    (I : Ideal R) (e : Z ≅ Spec (Ideal.closedRing R I))
    (hi : i = e.hom ≫ Ideal.closedMap R I) :
    Set.range i = PrimeSpectrum.zeroLocus (I : Set R) := by
  have hs : Function.Surjective e.hom := by
    intro x
    refine ⟨e.inv x, ?_⟩
    change (e.inv ≫ e.hom) x = x
    rw [e.inv_hom_id]
    rfl
  rw [hi]
  change Set.range ((Ideal.closedMap R I) ∘ e.hom) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr hs, Set.image_univ, Ideal.closedMap_range]

/-- Actual affine support gives eventual vanishing of genuine unit-kernel
iterations, by an actual annihilating ideal power. -/
theorem affine_kernelIterate_eventually_zero {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (i : Z ⟶ Spec R) [IsClosedImmersion i] (M : FiniteTypeSheaves (Spec R))
    (hM : finiteTypeSheavesSupportedAway (openMap i) M) :
    ∃ n, IsZero (kernelIterate (coherentAdjunction i).unit n M) := by
  obtain ⟨I, e, hi⟩ := (IsClosedImmersion.Spec_iff (f := i)).mp inferInstance
  have hI : finiteTypeSheavesSupportedAway (Ideal.openMap R I) M := by
    rw [finiteTypeSheavesSupportedAway_iff_support_subset, Ideal.openMap_range_compl]
    simpa only [affinePresentation_range R i I e hi] using (supported_iff i M).mp hM
  obtain ⟨n, hn⟩ := (Ideal.finiteTypeSheavesSupportedAway_iff_pow_le_annihilator R I M).mp hI
  exact ⟨n, kernelIterate_isZero_of_power_annihilator R i I e hi M n hn⟩

/-- A finite actual affine subcover produces a finite exponent on each
supported coherent sheaf of the noetherian ambient scheme. -/
theorem kernelIterate_eventually_zero {Z X : Scheme.{u}}
    [IsLocallyNoetherian Z] [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (M : FiniteTypeSheaves X)
    (hM : finiteTypeSheavesSupportedAway (openMap i) M) :
    ∃ n, IsZero (kernelIterate (coherentAdjunction i).unit n M) := by
  classical
  let A := X.affineOpenCover
  let (k : A.I₀) : IsNoetherianRing (A.X k) := noetherian_affineChart _ (A.f k)
  have hlocal (k : A.I₀) : ∃ n, IsZero
      (kernelIterate (coherentAdjunction (pullback.snd i (A.f k))).unit n
        ((finiteTypeSheavesRestriction (A.f k)).obj M)) := by
    exact affine_kernelIterate_eventually_zero (A.X k) (pullback.snd i (A.f k)) _
      (supported_restrict i (A.f k) M hM)
  choose n hn using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun k : A.I₀ ↦ Set.range (A.f k))
    (fun k ↦ IsOpenImmersion.isOpen_range (A.f k)) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨A.idx x, A.covers x⟩)
  let N := s.sup n
  refine ⟨N, ?_⟩
  apply IsZero.of_full_of_faithful_of_isZero (finiteTypeSheavesToModules X) _
  apply (SchemeSheaf.isZero_iff_stalks _).mpr
  intro x
  have hx := hs (show x ∈ (Set.univ : Set X) from trivial)
  simp only [Set.mem_iUnion, Set.mem_range] at hx
  obtain ⟨k, hk, y, hy⟩ := hx
  have hz : IsZero ((finiteTypeSheavesRestriction (A.f k)).obj
      (kernelIterate (coherentAdjunction i).unit N M)) :=
    (kernelIterate_isZero_of_le (coherentAdjunction (pullback.snd i (A.f k))).unit
      (Finset.le_sup hk) _ (hn k)).of_iso (kernelIterateOpenBaseChange i (A.f k) N M)
  have hz' := (finiteTypeSheavesToModules (Spec (A.X k))).map_isZero hz
  have hstalk := (SchemeSheaf.stalkFunctor (Spec (A.X k)) y).map_isZero hz'
  have hstalk' := hstalk.of_iso
    ((Scheme.Modules.restrictStalkNatIso (A.f k) y).app
      (kernelIterate (coherentAdjunction i).unit N M).obj).symm
  change IsZero ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
    x).obj
    (kernelIterate (coherentAdjunction i).unit N M).obj)
  simpa only [hy] using hstalk'

end Quillen.CoherentScheme.ClosedImmersion.General
