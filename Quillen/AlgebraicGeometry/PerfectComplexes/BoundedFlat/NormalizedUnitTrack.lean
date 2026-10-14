/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NormalizedUnitCoherence
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels

/-! The entire original geometric identity track and its actual normalized unit triangle. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum (Homotopy)
universe u

namespace Quillen.Waldhausen.IteratedS

private theorem homotopy_level_transport {X Y : Quillen.LoopPrespectrum}
    {f g g' : X ⟶ Y} (e : g = g')
    (p : Homotopy f g = Homotopy f g') (H : Homotopy f g) (n : ℕ) :
    (p.mp H).level n = H.level n := by
  subst g'
  rfl

/-- The full original normalization unit is induced by the actual inverse rebasing iso. -/
theorem exactOriginalPrespectrumMapIdHomotopy_level
    {C : Type u} [Category C] (W : Waldhausen.Structure C) (n : ℕ) :
    (exactOriginalPrespectrumMapIdHomotopy W).level n =
      (originalPrespectrumTransformationHomotopy W W
        (Waldhausen.IsExact.id W.cof W.weq).rebase (Waldhausen.IsExact.id W.cof W.weq)
        (Quillen.rebaseFunctor_obj_base _ _ _ _) rfl
        (Quillen.rebaseFunctorIso (𝟭 C) W.zero W.zero
          (((Waldhausen.IsExact.id W.cof W.weq).zero W.isZero).iso W.isZero)).inv
        (fun _ ↦ W.weq_iso _ inferInstance)).level n := by
  unfold exactOriginalPrespectrumMapIdHomotopy
  apply homotopy_level_transport (originalPrespectrumMap_id W)

end Quillen.Waldhausen.IteratedS

namespace Quillen.PerfectComplexes

/-- The total normalized geometric unit, with the literal original spectrum endpoints. -/
def boundedFlatNormalizedIdTrack (X : Scheme.{u}) :
    Homotopy (boundedFlatPerfectPrespectrumMap (𝟙 X))
      (𝟙 (originalPrespectrum (boundedFlatPerfectWaldhausen X))) :=
  (originalPrespectrumTransformationHomotopy (boundedFlatPerfectWaldhausen X)
    (boundedFlatPerfectWaldhausen X) (boundedFlatNormalizedPullback_exact (𝟙 X))
    (Waldhausen.IsExact.id _ _) (boundedFlatNormalizedPullback_obj_zero _) rfl
    (boundedFlatNormalizedPullbackIdIso X).hom
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)).cast
      rfl (originalPrespectrumMap_id _)

/-- Its original composition triangle recovers BOTH pieces of the fixed identity homotopy. -/
def boundedFlatNormalizedIdTrackComparison (X : Scheme.{u}) :
    (boundedFlatNormalizedIdTrack X).RelHomotopy (boundedFlatPerfectPrespectrumIdHomotopy X) := by
  let W := boundedFlatPerfectWaldhausen X
  let h := boundedFlatPerfectPullback_exact (𝟙 X)
  let hI := Waldhausen.IsExact.id W.cof W.weq
  let η := Waldhausen.normalizedWeakTransformation h hI (boundedFlatPerfectPullbackIdIso X).hom
  let θ := (Quillen.rebaseFunctorIso (𝟭 (BoundedFlatPerfect X)) W.zero W.zero
    ((hI.zero W.isZero).iso W.isZero)).inv
  have J := originalPrespectrumTransformationCompositionHomotopy W W
    h.rebase hI.rebase hI
    (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _) rfl
    η θ (Waldhausen.normalizedWeakTransformation_weak _ _ _
      (fun _ ↦ W.weq_iso _ inferInstance)) (fun _ ↦ W.weq_iso _ inferInstance)
  have he : η ≫ θ = (boundedFlatNormalizedPullbackIdIso X).hom :=
    (boundedFlatNormalizedPullbackIdIso_hom X).symm
  simp only [he] at J
  refine J.ofLevels _ _ (fun _ ↦ rfl) ?_
  intro n
  apply Homotopy.trans_level_congr
  · rfl
  · exact exactOriginalPrespectrumMapIdHomotopy_level W n

end Quillen.PerfectComplexes
