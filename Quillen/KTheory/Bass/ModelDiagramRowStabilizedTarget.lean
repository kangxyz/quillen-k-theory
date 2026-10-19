/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelDiagramStabilizedTarget
public import Quillen.KTheory.Bass.ModelDiagramRowRefinementNaturality

/-!
# Proper row targets for the actual finite-stage suspension replacement

At every original Bass stage the target is parameter looping of the genuine
row refinement of its unlooped cone. The replacement is the loop of the actual
evaluation counit followed by the computed row comparison. Its stability uses
the proved cone counit and finite row range; its unit triangle retains the
original comparison. No untransposed tail-loop spectrum is substituted for
the row target, and no tensor-cup qualification is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.KTheory.Bass.ModelDiagramRowStabilizedTarget
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ Model.{w})

/-- The same original unlooped cone, with its actual finite-stage model input. -/
abbrev cone (X : C) : LoopPrespectrum.{w} := ModelDiagramRowRefinement.source Q i F X

/-- The actual target has the computed row-compatible structure maps. -/
def target (X : C) : LoopPrespectrum.{w} :=
  parameterLooping (ModelDiagramRowRefinement.carrier Q i F X)

/-- Original coefficient arrows act on the whole proper row target. -/
def targetDiagram : C ⥤ LoopPrespectrum.{w} :=
  ModelDiagramRowRefinement.diagram Q i F ⋙ parameterLoopingFunctor

/-- The actual counit followed by the original row comparison gives replacement. -/
def refinement (X : C) :
    parameterLooping (suspensionCone (parameterLooping (cone Q i F X))) ⟶ target Q i F X :=
  parameterLoopingMap (suspensionLoopCounit (cone Q i F X) ≫
    ModelDiagramRowRefinement.comparison Q i F X)

/-- The proper replacement is stable from the proved actual counit and finite row range. -/
theorem refinement_stable (X : C) : IsStableEquivalence (refinement Q i F X) :=
  parameterLoopingMap_isStableEquivalence _
    ((ModelDiagramSuspension.cone_counit_stable Q i F X).comp
      (ModelDiagramRowRefinement.comparison_isStableEquivalence Q i F X))

/-- The original suspension unit followed by replacement is exactly the looped row comparison. -/
theorem unit_refinement (X : C) :
    suspensionLoopUnit (parameterLooping (cone Q i F X)) ≫ refinement Q i F X =
      parameterLoopingMap (ModelDiagramRowRefinement.comparison Q i F X) := by
  change suspensionLoopUnit (parameterLooping (cone Q i F X)) ≫
    parameterLoopingMap (suspensionLoopCounit (cone Q i F X) ≫
      ModelDiagramRowRefinement.comparison Q i F X) = _
  rw [show parameterLoopingMap (suspensionLoopCounit (cone Q i F X) ≫
      ModelDiagramRowRefinement.comparison Q i F X) =
    parameterLoopingMap (suspensionLoopCounit (cone Q i F X)) ≫
      parameterLoopingMap (ModelDiagramRowRefinement.comparison Q i F X) from
        parameterLoopingFunctor.map_comp _ _]
  rw [← Category.assoc, suspensionLoopUnit_counit, Category.id_comp]

/-- Literal original successor objects retain their existing whole-spectrum identification. -/
def currentRefinement (X : C) :
    parameterLooping (suspensionCone
      (((strictDiagramIterate Q (i + 1)).obj (F ⋙ prespectrumFunctor)).obj X)) ⟶
        target Q i F X :=
  eqToHom (congrArg (fun E => parameterLooping (suspensionCone E))
    (ModelDiagramSuspension.successor_obj Q i F X)) ≫ refinement Q i F X

/-- Replacement at each original successor is stable without new model hypotheses. -/
theorem currentRefinement_stable (X : C) :
    IsStableEquivalence (currentRefinement Q i F X) := by
  apply IsStableEquivalence.comp _ (refinement_stable Q i F X)
  intro d
  infer_instance

/-- The whole replacement commutes with the original coefficient map. -/
theorem refinement_naturality {X Y : C} (f : X ⟶ Y) :
    parameterLoopingMap (suspensionConeMap (parameterLoopingMap
      ((ModelDiagramRowRefinement.sourceDiagram Q i F).map f))) ≫ refinement Q i F Y =
    refinement Q i F X ≫ (targetDiagram Q i F).map f := by
  let g : cone Q i F X ⟶ cone Q i F Y :=
    (ModelDiagramRowRefinement.sourceDiagram Q i F).map f
  have hρ : g ≫ ModelDiagramRowRefinement.comparison Q i F Y =
      ModelDiagramRowRefinement.comparison Q i F X ≫
        ModelDiagramRowRefinement.map Q i F f :=
    ModelDiagramRowRefinement.comparison_naturality Q i F f
  change parameterLoopingFunctor.map (suspensionConeMap (parameterLoopingMap g)) ≫
      parameterLoopingFunctor.map (suspensionLoopCounit (cone Q i F Y) ≫
        ModelDiagramRowRefinement.comparison Q i F Y) =
    parameterLoopingFunctor.map (suspensionLoopCounit (cone Q i F X) ≫
      ModelDiagramRowRefinement.comparison Q i F X) ≫
        parameterLoopingFunctor.map (ModelDiagramRowRefinement.map Q i F f)
  rw [← parameterLoopingFunctor.map_comp, ← parameterLoopingFunctor.map_comp]
  apply congrArg parameterLoopingFunctor.map
  rw [← Category.assoc, suspensionLoopCounit_naturality, Category.assoc, hρ,
    Category.assoc]

/-- The actual zero-level triple loop and positive double loops retain T1 separation. -/
instance spaceT1Space (X : C) (n : ℕ) : T1Space ((target Q i F X).space n) := by
  cases n with
  | zero =>
    change T1Space (Path (Path.refl (Path.refl ((cone Q i F X).point 2)))
      (Path.refl (Path.refl ((cone Q i F X).point 2))))
    infer_instance
  | succ k =>
    change T1Space (Path (Path.refl ((cone Q i F X).point (k + 2)))
      (Path.refl ((cone Q i F X).point (k + 2))))
    infer_instance

/-- Point HEP retains the extra actual zero-level loop rather than deleting it. -/
theorem point_homotopyExtensionProperty (X : C) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom
      (ContinuousMap.const PUnit.{w + 1} ((target Q i F X).point n))) := by
  cases n with
  | zero =>
    have : T1Space ((ModelDiagramRowRefinement.carrier Q i F X).space 0) := by
      change T1Space (Path (Path.refl ((cone Q i F X).point 2))
        (Path.refl ((cone Q i F X).point 2)))
      infer_instance
    have hp : Quillen.homotopyExtensionProperty (TopCat.ofHom
        (ContinuousMap.const PUnit.{w + 1}
          ((ModelDiagramRowRefinement.carrier Q i F X).point 0))) :=
      ModelDiagramStabilizedTarget.point_homotopyExtensionProperty Q i F X 1
    exact Quillen.path_refl_homotopyExtensionProperty isClosed_singleton hp
  | succ k =>
    exact ModelDiagramStabilizedTarget.point_homotopyExtensionProperty Q i F X (k + 1)

/-- At the positive growth cutoff the actual proper target has the original double-loop spaces. -/
theorem homotopyGroup_subsingleton_at (X : C) (n k : ℕ) (hk : k < n + 2)
    (x : (target Q i F X).space (n + (i + 1) + 2)) :
    Subsingleton (HomotopyGroup.Pi k ((target Q i F X).space (n + (i + 1) + 2)) x) :=
  ModelDiagramStabilizedTarget.homotopyGroup_subsingleton_at Q i F X n k hk x

/-- Larger offsets retain the actual positive-level growth bound. -/
theorem homotopyGroup_subsingleton_at_offset (X : C) (c : ℕ) (hc : i + 1 ≤ c)
    (n k : ℕ) (hk : k < n + 2) (x : (target Q i F X).space (n + c + 2)) :
    Subsingleton (HomotopyGroup.Pi k ((target Q i F X).space (n + c + 2)) x) :=
  ModelDiagramStabilizedTarget.homotopyGroup_subsingleton_at_offset Q i F X c hc n k hk x

private theorem unit_transport {E G : LoopPrespectrum.{w}} (h : E = G) :
    suspensionLoopUnit E ≫
        eqToHom (congrArg (fun A => parameterLooping (suspensionCone A)) h) =
      eqToHom h ≫ suspensionLoopUnit G := by
  subst G
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The literal original successor unit retains its actual spectrum transport in the triangle. -/
theorem current_unit_refinement (X : C) :
    suspensionLoopUnit
        (((strictDiagramIterate Q (i + 1)).obj (F ⋙ prespectrumFunctor)).obj X) ≫
      currentRefinement Q i F X =
    eqToHom (ModelDiagramSuspension.successor_obj Q i F X) ≫
      parameterLoopingMap (ModelDiagramRowRefinement.comparison Q i F X) := by
  unfold currentRefinement
  rw [← Category.assoc, unit_transport (ModelDiagramSuspension.successor_obj Q i F X),
    Category.assoc, unit_refinement]
  rfl

end Quillen.KTheory.Bass.ModelDiagramRowStabilizedTarget
