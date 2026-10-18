/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.IteratedLoopStrength
public import Quillen.Topology.Prespectrum.LoopTranspose
public import Quillen.KTheory.Bass.StrictDiagramStableEquivalence

/-!
# Actual finite stage maps into loop-normalized cone iterates

The map from the original finite Bass stage to `Omega^i C^i F` is formed from the original
Bass image of the preceding map and the fixed-order iterated loop strength. Both full functor
identifications are retained as explicit equality transports. Genuine Model input makes each
stage map stable through existing Bass stable preservation and the proved topology of both
actual finite stages. These are stage maps only: no compatibility with successive seed
transitions, no equality of geometric chi with cone-loop strength, and no tower comparison
is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace Quillen.KTheory.Bass.NormalizedStageMap
open FiniteConeTopology FiniteConeStrength IteratedLoopStrength
variable {C : Type u} [Category.{v} C]

/-- The finite normalized object uses the same unlooped cone as the original cone action. -/
def normalized (Q : C ⥤ Arrow (Arrow C)) (i : ℕ) (F : C ⥤ LoopPrespectrum.{w}) :
    C ⥤ LoopPrespectrum.{w} := loopDiagram i (iterate Q i F)

/-- Every normalized value is the literal finite cone followed by the original parameter loops. -/
theorem normalized_obj (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w}) (X : C) :
    (normalized Q i F).obj X = loops i ((iterate Q i F).obj X) :=
  loopDiagram_obj i _ X

/-- The two associations of the original finite Bass iterate are equal as entire functors. -/
theorem bass_succ_eq (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w}) :
    (strictDiagramIterate Q (i + 1)).obj F =
      (strictDiagramFunctor Q).obj ((strictDiagramIterate Q i).obj F) := by
  induction i generalizing F with
  | zero => rfl
  | succ i ih => exact ih ((strictDiagramFunctor Q).obj F)

/-- The original Bass functor is the same unlooped cone followed by parameter looping. -/
theorem bass_eq_loop_cone (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w}) :
    (strictDiagramFunctor Q).obj F = ConeTrack.diagram Q F ⋙
      parameterLoopingFunctor := rfl

/-- The target of the prescribed iterated strength is the next normalized stage. -/
theorem normalized_succ_eq (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w}) :
    loopDiagram i ((strictDiagramFunctor Q).obj (iterate Q i F)) =
      normalized Q (i + 1) F := by
  rw [bass_eq_loop_cone]
  exact loopDiagram_postcomp i (ConeTrack.diagram Q (iterate Q i F))

/-- Actual stage maps, retaining both complete source and target equality transports. -/
def stageMap (Q : C ⥤ Arrow (Arrow C)) :
    ∀ (i : ℕ) (F : C ⥤ LoopPrespectrum.{w}),
      (strictDiagramIterate Q i).obj F ⟶ normalized Q i F
  | 0, F => 𝟙 F
  | i + 1, F => eqToHom (bass_succ_eq Q i F) ≫
      (strictDiagramFunctor Q).map (stageMap Q i F) ≫
      iteratedStrength Q i (iterate Q i F) ≫ eqToHom (normalized_succ_eq Q i F)

private theorem eqToHom_app_stable {F G : C ⥤ LoopPrespectrum.{w}} (h : F = G) (X : C) :
    IsStableEquivalence ((eqToHom h).app X) := by
  subst G
  intro d
  change IsIso ((stableHomotopyFunctor d).map (𝟙 _))
  infer_instance

/-- Every actual stage map is stable for genuine Model input, without later-stage assumptions. -/
theorem model_stageMap_stable (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (M : C ⥤ Model.{w}) (X : C) :
    IsStableEquivalence ((stageMap Q i (M ⋙ prespectrumFunctor)).app X) := by
  induction i generalizing X with
  | zero =>
    intro d
    change IsIso ((stableHomotopyFunctor d).map (𝟙 _))
    infer_instance
  | succ i ih =>
    have hR : ∀ Y n, Quillen.homotopyExtensionProperty
        (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1}
          (((normalized Q i (M ⋙ prespectrumFunctor)).obj Y).point n))) := by
      intro Y n
      rw [normalized_obj]
      exact modelLoopsIterate_point_homotopyExtensionProperty Q i i M Y n
    have hπR : ∀ Y n k, k < n + 2 →
        ∀ x : ((normalized Q i (M ⋙ prespectrumFunctor)).obj Y).space (n + i + 2),
          Subsingleton (HomotopyGroup.Pi k
            (((normalized Q i (M ⋙ prespectrumFunctor)).obj Y).space (n + i + 2)) x) := by
      intro Y n k hk
      rw [normalized_obj]
      exact modelLoopsIterate_homotopyGroup_subsingleton Q i i M Y n k hk
    have hB := strictDiagramFunctor_map_isStableEquivalence_of_linearGrowth Q
      ((strictDiagramIterate Q i).obj (M ⋙ prespectrumFunctor))
      (normalized Q i (M ⋙ prespectrumFunctor))
      (modelDiagramIterate_point_homotopyExtensionProperty Q i M) hR i i
      (fun Y n k hk x => modelDiagramIterate_homotopyGroup_subsingleton_at
        Q i M Y n k hk x) hπR (stageMap Q i (M ⋙ prespectrumFunctor)) ih X
    exact (eqToHom_app_stable (bass_succ_eq Q i (M ⋙ prespectrumFunctor)) X).comp
      (hB.comp ((iterated_model_stable Q i i M X).comp
        (eqToHom_app_stable (normalized_succ_eq Q i (M ⋙ prespectrumFunctor)) X)))

end Quillen.KTheory.Bass.NormalizedStageMap
