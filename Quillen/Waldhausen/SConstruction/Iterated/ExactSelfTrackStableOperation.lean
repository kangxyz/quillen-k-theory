/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.ExactCompositionHomotopy
public import Quillen.Topology.Prespectrum.SelfTrackRelativeHomotopy
public import Quillen.Topology.Prespectrum.SelfTrackStableConcatenation

/-! # Stable operations of actual canonically rebased exact-functor automorphisms -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
universe u v
namespace Quillen.Waldhausen.IteratedS
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (W : Structure C) (V : Structure D) {F : C ⥤ D}
variable (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- The original composition triangle gives the actual reversed sum on all stable groups. -/
theorem exactIsoSelfTrack_stableOperation_comp (e e' : F ≅ F) (d : ℤ) :
    (exactOriginalPrespectrumIsoHomotopy W V hF hF (e ≪≫ e')).stableOperation d =
      (exactOriginalPrespectrumIsoHomotopy W V hF hF e').stableOperation d +
        (exactOriginalPrespectrumIsoHomotopy W V hF hF e).stableOperation d :=
  ((exactOriginalPrespectrumIsoCompositionHomotopy W V hF hF hF e e').stableOperation_eq d).trans
    (Homotopy.stableOperation_trans _ _ d)

/-- Idempotence of the original identity composition triangle forces its operation to zero. -/
theorem exactIsoSelfTrack_stableOperation_refl (d : ℤ) :
    (exactOriginalPrespectrumIsoHomotopy W V hF hF (Iso.refl F)).stableOperation d = 0 := by
  have h := exactIsoSelfTrack_stableOperation_comp W V hF (Iso.refl F) (Iso.refl F) d
  simp only [Iso.refl_trans] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

/-- The actual inverse natural isomorphism gives the negative original stable operation. -/
theorem exactIsoSelfTrack_stableOperation_symm (e : F ≅ F) (d : ℤ) :
    (exactOriginalPrespectrumIsoHomotopy W V hF hF e.symm).stableOperation d =
      -(exactOriginalPrespectrumIsoHomotopy W V hF hF e).stableOperation d := by
  have h := exactIsoSelfTrack_stableOperation_comp W V hF e e.symm d
  rw [Iso.self_symm_id, exactIsoSelfTrack_stableOperation_refl] at h
  exact eq_neg_of_add_eq_zero_left h.symm

end Quillen.Waldhausen.IteratedS
