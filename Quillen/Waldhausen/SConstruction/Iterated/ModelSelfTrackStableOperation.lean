/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumCompositionHomotopy
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIsoNaturality
public import Quillen.Topology.Prespectrum.SelfTrackRelativeHomotopy
public import Quillen.Topology.Prespectrum.SelfTrackStableConcatenation

/-!
# Stable operations of the original Model automorphism tracks

The actual transformation-composition triangle identifies the stable operation of a composite
Model automorphism with the reversed sum. In particular, the actual inverse automorphism has
the negative stable operation. These statements use the original zero-preserving Model maps,
without transporting through normalized exact functors or changing the Laurent track.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
universe u
namespace Quillen.Waldhausen.IteratedS
variable {V W : Model.{u}} (F : V ⟶ W)

/-- The original Model composition triangle gives the actual reversed stable sum. -/
theorem prespectrumIsoHomotopy_stableOperation_comp
    (e e' : F.functor ≅ F.functor) (d : ℤ) :
    (prespectrumIsoHomotopy F (e ≪≫ e')).stableOperation d =
      (prespectrumIsoHomotopy F e').stableOperation d +
        (prespectrumIsoHomotopy F e).stableOperation d :=
  ((prespectrumTransformationCompositionHomotopy e.hom e'.hom
    (fun _ ↦ W.waldhausen.weq_iso _ inferInstance)
    (fun _ ↦ W.waldhausen.weq_iso _ inferInstance)).stableOperation_eq d).trans
      (Homotopy.stableOperation_trans _ _ d)

/-- The original identity automorphism induces zero on the integer-graded stable operation. -/
theorem prespectrumIsoHomotopy_stableOperation_refl (d : ℤ) :
    (prespectrumIsoHomotopy F (Iso.refl F.functor)).stableOperation d = 0 := by
  have h := prespectrumIsoHomotopy_stableOperation_comp F
    (Iso.refl F.functor) (Iso.refl F.functor) d
  simp only [Iso.refl_trans] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

/-- The actual inverse Model automorphism gives the negative original stable operation. -/
theorem prespectrumIsoHomotopy_stableOperation_symm
    (e : F.functor ≅ F.functor) (d : ℤ) :
    (prespectrumIsoHomotopy F e.symm).stableOperation d =
      -(prespectrumIsoHomotopy F e).stableOperation d := by
  have h := prespectrumIsoHomotopy_stableOperation_comp F e e.symm d
  rw [Iso.self_symm_id, prespectrumIsoHomotopy_stableOperation_refl] at h
  exact eq_neg_of_add_eq_zero_left h.symm

end Quillen.Waldhausen.IteratedS
