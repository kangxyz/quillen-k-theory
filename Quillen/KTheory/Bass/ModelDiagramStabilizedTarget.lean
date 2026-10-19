/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelDiagramSuspension
public import Quillen.Topology.Prespectrum.StableStabilization

/-!
# The actual stabilized target for current Bass-stage suspension diagrams

The target is parameter looping of the original untransposed looping of the tail of
`C(B^i F)`. Its actual level spaces have two path coordinates and the original one-level
shift. Original Model topology gives T1 separation, point HEP and all-point growth with
offset i+1. No equality between the two looping prespectra is used.

The map from the actual looped suspension is parameter looping of the evaluation counit
followed by original stabilization. It is stable without extra hypotheses on Model input.
The original unit/counit triangle gives its precise composite with the suspension unit.
These statements supply target replacement inputs; they certify no tensor-cup identity.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.KTheory.Bass.ModelDiagramStabilizedTarget
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ Model.{w})

/-- The actual unlooped cone of the original i-th Bass iterate. -/
abbrev cone (X : C) : LoopPrespectrum.{w} :=
  (ConeTrack.diagram Q ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor))).obj X

/-- The stabilized target retains the original untransposed inner looping structure. -/
def target (X : C) : LoopPrespectrum.{w} :=
  parameterLooping (looping (tail (cone Q i F X)))

/-- Original Model separation passes through this actual cone. -/
instance coneSpaceT1Space (X : C) (n : ℕ) : T1Space ((cone Q i F X).space n) := by
  let : ∀ Y m, T1Space
      ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj Y).space m) :=
    fun Y m ↦ modelDiagramIterateSpaceT1Space Q i F Y m
  exact FiniteConeTopology.diagramSpaceT1Space Q _ X n

/-- Both actual loop coordinates retain T1 separation after the original level shift. -/
instance spaceT1Space (X : C) (n : ℕ) : T1Space ((target Q i F X).space n) := by
  change T1Space (Path (Path.refl ((cone Q i F X).point (n + 1)))
    (Path.refl ((cone Q i F X).point (n + 1))))
  infer_instance

/-- The original point in the stabilized target has HEP at every level. -/
theorem point_homotopyExtensionProperty (X : C) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom
      (ContinuousMap.const PUnit.{w + 1} ((target Q i F X).point n))) := by
  have hp := FiniteConeTopology.iterate_point_homotopyExtensionProperty Q 1
    ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor))
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F) X (n + 1)
  let : T1Space ((looping (tail (cone Q i F X))).space n) := by
    change T1Space (Path ((cone Q i F X).point (n + 1))
      ((cone Q i F X).point (n + 1)))
    infer_instance
  have h₁ := Quillen.path_refl_homotopyExtensionProperty
    (isClosed_singleton (x := (cone Q i F X).point (n + 1))) hp
  exact Quillen.path_refl_homotopyExtensionProperty isClosed_singleton h₁

/-- The two loops and one tail shift give the original all-point offset i+1. -/
theorem homotopyGroup_subsingleton_at (X : C) (n k : ℕ) (hk : k < n + 2)
    (x : (target Q i F X).space (n + (i + 1) + 2)) :
    Subsingleton (HomotopyGroup.Pi k
      ((target Q i F X).space (n + (i + 1) + 2)) x) := by
  have hπ := FiniteConeTopology.iterate_homotopyGroup_subsingleton Q 1
    ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor))
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F) i
    (fun Y m j hj y ↦ modelDiagramIterate_homotopyGroup_subsingleton_at
      Q i F Y m j hj y) X (n + 2) (k + 2) (by omega)
  have he : (n + 2) + i + 2 = (n + (i + 1) + 2) + 1 := by omega
  rw [he] at hπ
  apply Quillen.subsingleton_pi_loop_of_succ
    (Path.refl ((cone Q i F X).point ((n + (i + 1) + 2) + 1))) k
  exact Quillen.subsingleton_pi_loop_of_succ
    ((cone Q i F X).point ((n + (i + 1) + 2) + 1)) (k + 1)
    (hπ ((cone Q i F X).point _)) _

/-- The same all-point bound at an arbitrary level above the original cutoff. -/
theorem homotopyGroup_subsingleton_of_le (X : C) (m : ℕ) (hm : i + 3 ≤ m)
    (k : ℕ) (hk : k + (i + 1) < m) (x : (target Q i F X).space m) :
    Subsingleton (HomotopyGroup.Pi k ((target Q i F X).space m) x) := by
  have h := homotopyGroup_subsingleton_at Q i F X (m - (i + 3)) k (by omega)
  rw [show m - (i + 3) + (i + 1) + 2 = m by omega] at h
  exact h x

/-- Larger stage offsets can be used directly by the homotopy-pushout recurrence. -/
theorem homotopyGroup_subsingleton_at_offset (X : C) (c : ℕ) (hc : i + 1 ≤ c)
    (n k : ℕ) (hk : k < n + 2) (x : (target Q i F X).space (n + c + 2)) :
    Subsingleton (HomotopyGroup.Pi k ((target Q i F X).space (n + c + 2)) x) :=
  homotopyGroup_subsingleton_of_le Q i F X (n + c + 2) (by omega) k (by omega) x

/-- The actual target replacement is the parameter loop of counit then stabilization. -/
def refinement (X : C) :
    parameterLooping (suspensionCone (parameterLooping (cone Q i F X))) ⟶ target Q i F X :=
  parameterLoopingMap (suspensionLoopCounit (cone Q i F X) ≫
    stabilizationMap (cone Q i F X))

/-- Both original stable maps and actual parameter looping give stability of replacement. -/
theorem refinement_stable (X : C) : IsStableEquivalence (refinement Q i F X) :=
  parameterLoopingMap_isStableEquivalence _
    ((ModelDiagramSuspension.cone_counit_stable Q i F X).comp
      (stabilizationMap_isStableEquivalence (cone Q i F X)))

/-- The original cylinder unit followed by replacement is exactly looped stabilization. -/
theorem unit_refinement (X : C) :
    suspensionLoopUnit (parameterLooping (cone Q i F X)) ≫ refinement Q i F X =
      parameterLoopingMap (stabilizationMap (cone Q i F X)) := by
  change suspensionLoopUnit (parameterLooping (cone Q i F X)) ≫
    parameterLoopingMap (suspensionLoopCounit (cone Q i F X) ≫
      stabilizationMap (cone Q i F X)) = _
  rw [show parameterLoopingMap (suspensionLoopCounit (cone Q i F X) ≫
      stabilizationMap (cone Q i F X)) =
      parameterLoopingMap (suspensionLoopCounit (cone Q i F X)) ≫
        parameterLoopingMap (stabilizationMap (cone Q i F X)) from
      parameterLoopingFunctor.map_comp _ _]
  rw [← Category.assoc, suspensionLoopUnit_counit, Category.id_comp]

/-- Replacement at the literal original successor, retaining its whole-spectrum cast. -/
def currentRefinement (X : C) :
    parameterLooping (suspensionCone
      (((strictDiagramIterate Q (i + 1)).obj (F ⋙ prespectrumFunctor)).obj X)) ⟶
        target Q i F X :=
  eqToHom (congrArg (fun E ↦ parameterLooping (suspensionCone E))
    (ModelDiagramSuspension.successor_obj Q i F X)) ≫ refinement Q i F X

/-- No added Model topology premise is needed for literal current-stage replacement. -/
theorem currentRefinement_stable (X : C) :
    IsStableEquivalence (currentRefinement Q i F X) := by
  apply IsStableEquivalence.comp _ (refinement_stable Q i F X)
  intro d
  infer_instance

end Quillen.KTheory.Bass.ModelDiagramStabilizedTarget
