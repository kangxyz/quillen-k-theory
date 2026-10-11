/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.ObjectExtensionAux

/-!
# Finite affine-cover induction for coherent subobjects

The induction is on an actual finite union of affine opens. Its enlargement
step is separated so that the geometric kernel construction can be supplied
without repeating the compact-open induction.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Quillen.CoherentScheme

open Scheme.Modules

/-- The compact-open induction preserves the original open restriction and
accumulates coherence on the genuine union of affine opens. -/
theorem affineLocallyFiniteType_subobject_on_compact_open_of_enlargement
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (henlarge : ∀ (N : X.Modules) [N.IsQuasicoherent]
      (W : X.Opens), affineLocallyFiniteType W.toScheme (N.restrict W.ι) →
      ∀ (R : CommRingCat.{u}) [IsNoetherianRing R]
      (a : Spec R ⟶ X) [IsOpenImmersion a],
      ∃ (N' : X.Modules) (s : N' ⟶ N), N'.IsQuasicoherent ∧ Mono s ∧
        IsIso ((restrictFunctor W.ι).map s) ∧
        affineLocallyFiniteType (W ⊔ a.opensRange).toScheme
          (N'.restrict (W ⊔ a.opensRange).ι))
    (M : X.Modules) [M.IsQuasicoherent]
    (W : X.Opens) (hW : affineLocallyFiniteType W.toScheme (M.restrict W.ι))
    (S : X.Opens) (hS : IsCompact (S : Set X)) :
    ∃ (N : X.Modules) (s : N ⟶ M), N.IsQuasicoherent ∧ Mono s ∧
      IsIso ((restrictFunctor W.ι).map s) ∧
      affineLocallyFiniteType (W ⊔ S).toScheme (N.restrict (W ⊔ S).ι) := by
  refine compact_open_induction_on S hS ?_ ?_
  · refine ⟨M, 𝟙 M, inferInstance, inferInstance, ?_, ?_⟩
    · exact (restrictFunctor W.ι).map_isIso (𝟙 M)
    · rw [sup_bot_eq]
      exact hW
  · intro S hS V ih
    obtain ⟨N, s, hN, hs, hsW, hNW⟩ := ih
    have : N.IsQuasicoherent := hN
    have : Mono s := hs
    have : IsIso ((restrictFunctor W.ι).map s) := hsW
    have : IsNoetherianRing Γ(X, (V : X.Opens)) :=
      IsLocallyNoetherian.component_noetherian V
    obtain ⟨N', t, hN', ht, htW, hN'W⟩ :=
      henlarge N (W ⊔ S) hNW Γ(X, (V : X.Opens)) V.property.fromSpec
    have : Mono t := ht
    have : IsIso ((restrictFunctor (W ⊔ S).ι).map t) := htW
    have : IsIso ((restrictFunctor W.ι).map t) :=
      isIso_restrict_map_of_le (le_sup_left : W ≤ W ⊔ S) t
    refine ⟨N', t ≫ s, hN', inferInstance, ?_, ?_⟩
    · rw [Functor.map_comp]
      infer_instance
    · rw [V.property.opensRange_fromSpec, sup_assoc] at hN'W
      exact hN'W

/-- Covering a quasi-compact scheme by finitely many affine opens completes
the coherent subobject extension. -/
theorem affineLocallyFiniteType_subobject_extension_of_affine_enlargement
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (henlarge : ∀ (N : X.Modules) [N.IsQuasicoherent]
      (W : X.Opens), affineLocallyFiniteType W.toScheme (N.restrict W.ι) →
      ∀ (R : CommRingCat.{u}) [IsNoetherianRing R]
      (a : Spec R ⟶ X) [IsOpenImmersion a],
      ∃ (N' : X.Modules) (s : N' ⟶ N), N'.IsQuasicoherent ∧ Mono s ∧
        IsIso ((restrictFunctor W.ι).map s) ∧
        affineLocallyFiniteType (W ⊔ a.opensRange).toScheme
          (N'.restrict (W ⊔ a.opensRange).ι))
    (M : X.Modules) [M.IsQuasicoherent]
    (W : X.Opens) (hW : affineLocallyFiniteType W.toScheme (M.restrict W.ι)) :
    ∃ (N : FiniteTypeSheaves X) (s : N.obj ⟶ M), Mono s ∧
      IsIso ((restrictFunctor W.ι).map s) := by
  obtain ⟨N, s, hN, hs, hsW, hNW⟩ :=
    affineLocallyFiniteType_subobject_on_compact_open_of_enlargement
      henlarge M W hW ⊤ isCompact_univ
  have hcoh : affineLocallyFiniteType X N := affineLocallyFiniteType_of_restrict_top N (by
    rw [show W ⊔ (⊤ : X.Opens) = ⊤ from sup_top_eq W] at hNW
    exact hNW)
  exact ⟨⟨N, hcoh⟩, s, hs, hsW⟩

end Quillen.CoherentScheme
