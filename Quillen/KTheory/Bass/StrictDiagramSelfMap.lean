/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.StrictDiagramSuccessorMap
public import Quillen.KTheory.Bass.StrictDiagramTelescopeNaturality
public import Quillen.KTheory.Bass.StrictDiagramMap
public import Quillen.KTheory.Bass.StrictDiagramTopology
public import Quillen.Topology.Prespectrum.TelescopeTail

/-!
# The actual iterated seed gives a stable telescope-to-Bass map

The single original seed is carried through its genuine Bass iterates and the exact
right-successor transports. Forward tail passage proves stability using only stage T1.
A proved original seed square yields a whole telescope square; no finite seed is assumed stable.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
universe u v w
namespace Quillen.KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    {F : C ⥤ LoopPrespectrum.{w}} (η : F ⟶ (strictDiagramFunctor Q).obj F)

/-- The same original iterated seed, with its exact right-successor target transport. -/
def strictDiagramShiftedSeed (i : ℕ) :
    (strictDiagramIterate Q i).obj F ⟶
      (strictDiagramFunctor Q).obj ((strictDiagramIterate Q i).obj F) :=
  strictDiagramTransition Q η i ≫ strictDiagramSuccessorMap Q F i

/-- These actual transported seed arrows preserve the unchanged original tower transitions. -/
theorem strictDiagramShiftedSeed_compatibility (i : ℕ) :
    strictDiagramShiftedSeed Q η i ≫
        (strictDiagramFunctor Q).map (strictDiagramTransition Q η i) =
      strictDiagramTransition Q η i ≫ strictDiagramShiftedSeed Q η (i + 1) := by
  dsimp only [strictDiagramShiftedSeed]
  rw [Category.assoc, ← strictDiagramSuccessorMap_transition Q η i]

/-- An original seed square is retained after every actual iteration and successor transport. -/
theorem strictDiagramShiftedSeed_map {G : C ⥤ LoopPrespectrum.{w}}
    (θ : G ⟶ (strictDiagramFunctor Q).obj G) (a : F ⟶ G)
    (h : η ≫ (strictDiagramFunctor Q).map a = a ≫ θ) (i : ℕ) :
    strictDiagramShiftedSeed Q η i ≫
        (strictDiagramFunctor Q).map ((strictDiagramIterate Q i).map a) =
      (strictDiagramIterate Q i).map a ≫ strictDiagramShiftedSeed Q θ i := by
  dsimp only [strictDiagramShiftedSeed]
  rw [Category.assoc, ← strictDiagramSuccessorMap_naturality Q a i,
    ← Category.assoc, strictDiagramTransition_map Q η θ a h i, Category.assoc]

/-- The actual original tower maps into its Bass-image tower using this single iterated seed. -/
def strictDiagramTelescopeSeedMap :
    Telescope.diagramFunctor (fun i => (strictDiagramIterate Q i).obj F)
        (strictDiagramTransition Q η) ⟶
      Telescope.diagramFunctor
        (fun i => (strictDiagramFunctor Q).obj ((strictDiagramIterate Q i).obj F))
        (fun i => (strictDiagramFunctor Q).map (strictDiagramTransition Q η i)) :=
  Telescope.diagramMap _ _ _ _ (strictDiagramShiftedSeed Q η)
    (strictDiagramShiftedSeed_compatibility Q η)

/-- The original iterated seed and genuine comparison give the actual telescope-to-Bass map. -/
def strictDiagramTelescopeSelfMap :
    Telescope.diagramFunctor (fun i => (strictDiagramIterate Q i).obj F)
        (strictDiagramTransition Q η) ⟶
      (strictDiagramFunctor Q).obj
        (Telescope.diagramFunctor (fun i => (strictDiagramIterate Q i).obj F)
          (strictDiagramTransition Q η)) :=
  strictDiagramTelescopeSeedMap Q η ≫
    strictDiagramTelescopeComparison Q (fun i => (strictDiagramIterate Q i).obj F)
      (strictDiagramTransition Q η)

/-- Every original seed-preserving arrow commutes with the entire actual telescope self-map. -/
theorem strictDiagramTelescopeSelfMap_naturality {G : C ⥤ LoopPrespectrum.{w}}
    (θ : G ⟶ (strictDiagramFunctor Q).obj G) (a : F ⟶ G)
    (h : η ≫ (strictDiagramFunctor Q).map a = a ≫ θ) :
    strictDiagramTelescopeSelfMap Q η ≫ (strictDiagramFunctor Q).map
        (Telescope.diagramMap (fun i => (strictDiagramIterate Q i).obj F)
          (fun i => (strictDiagramIterate Q i).obj G)
          (strictDiagramTransition Q η) (strictDiagramTransition Q θ)
          (fun i => (strictDiagramIterate Q i).map a)
          (fun i => (strictDiagramTransition_map Q η θ a h i).symm)) =
      Telescope.diagramMap (fun i => (strictDiagramIterate Q i).obj F)
          (fun i => (strictDiagramIterate Q i).obj G)
          (strictDiagramTransition Q η) (strictDiagramTransition Q θ)
          (fun i => (strictDiagramIterate Q i).map a)
          (fun i => (strictDiagramTransition_map Q η θ a h i).symm) ≫
        strictDiagramTelescopeSelfMap Q θ :=
  strictDiagramTelescopeComparison_square Q _ _ _ _ _ _
    (strictDiagramShiftedSeed Q η) (strictDiagramShiftedSeed Q θ)
    (strictDiagramShiftedSeed_compatibility Q η)
    (strictDiagramShiftedSeed_compatibility Q θ)
    (strictDiagramShiftedSeed_map Q η θ a h)

/-- The unchanged original stage face retains its seed and Bass of that same inclusion. -/
theorem strictDiagramTelescopeSelfMap_inclusion (i : ℕ) (X : C) :
    (Telescope.diagramInclusion (fun i => (strictDiagramIterate Q i).obj F)
        (strictDiagramTransition Q η) i).app X ≫
        (strictDiagramTelescopeSelfMap Q η).app X =
      (strictDiagramShiftedSeed Q η i).app X ≫
        ((strictDiagramFunctor Q).map
          (Telescope.diagramInclusion (fun i => (strictDiagramIterate Q i).obj F)
            (strictDiagramTransition Q η) i)).app X := by
  have h := NatTrans.congr_app (Telescope.diagramInclusion_diagramMap
    (fun i => (strictDiagramIterate Q i).obj F)
    (fun i => (strictDiagramFunctor Q).obj ((strictDiagramIterate Q i).obj F))
    (strictDiagramTransition Q η)
    (fun i => (strictDiagramFunctor Q).map (strictDiagramTransition Q η i))
    (strictDiagramShiftedSeed Q η) (strictDiagramShiftedSeed_compatibility Q η) i) X
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (strictDiagramTelescopeComparison Q
      (fun i => (strictDiagramIterate Q i).obj F) (strictDiagramTransition Q η)).app X) h).trans
      ((Category.assoc _ _ _).trans (congrArg ((strictDiagramShiftedSeed Q η i).app X ≫ ·)
        (strictDiagramTelescopeComparison_inclusion Q
          (fun i => (strictDiagramIterate Q i).obj F) (strictDiagramTransition Q η) i X))))

/-- The original initial cylinder face retains exactly the single original seed. -/
theorem strictDiagramTelescopeSelfMap_initial (X : C) :
    (Telescope.diagramInclusion (fun i => (strictDiagramIterate Q i).obj F)
        (strictDiagramTransition Q η) 0).app X ≫
        (strictDiagramTelescopeSelfMap Q η).app X =
      η.app X ≫ ((strictDiagramFunctor Q).map
        (Telescope.diagramInclusion (fun i => (strictDiagramIterate Q i).obj F)
          (strictDiagramTransition Q η) 0)).app X := by
  rw [strictDiagramTelescopeSelfMap_inclusion]
  change (η.app X ≫ 𝟙 _) ≫ _ = _
  rw [Category.comp_id]

variable [∀ i X k, T1Space ((((strictDiagramIterate Q i).obj F).obj X).space k)]

/-- The exact seed telescope map is stable by original forward-tail passage and successor isos. -/
theorem strictDiagramTelescopeSeedMap_isStableEquivalence (X : C) :
    IsStableEquivalence ((strictDiagramTelescopeSeedMap Q η).app X) := by
  let : ∀ i k, T1Space
      ((((strictDiagramFunctor Q).obj ((strictDiagramIterate Q i).obj F)).obj X).space k) :=
    fun i k => strictDiagramFunctorSpaceT1Space Q ((strictDiagramIterate Q i).obj F) X k
  let e := Telescope.map
    (fun i => ((strictDiagramIterate Q (i + 1)).obj F).obj X)
    (fun i => (strictDiagramTransition Q η (i + 1)).app X)
    (fun i => ((strictDiagramFunctor Q).obj ((strictDiagramIterate Q i).obj F)).obj X)
    (fun i => ((strictDiagramFunctor Q).map (strictDiagramTransition Q η i)).app X)
    (fun i => (strictDiagramSuccessorMap Q F i).app X)
    (fun i => (NatTrans.congr_app (strictDiagramSuccessorMap_transition Q η i) X).symm)
  have he : IsStableEquivalence e := by
    apply Telescope.map_isStableEquivalence
      (fun i => ((strictDiagramIterate Q (i + 1)).obj F).obj X)
      (fun i => (strictDiagramTransition Q η (i + 1)).app X)
      (fun i => ((strictDiagramFunctor Q).obj ((strictDiagramIterate Q i).obj F)).obj X)
      (fun i => ((strictDiagramFunctor Q).map (strictDiagramTransition Q η i)).app X)
      (fun i => (strictDiagramSuccessorMap Q F i).app X)
      (fun i => (NatTrans.congr_app (strictDiagramSuccessorMap_transition Q η i) X).symm)
    intro i d
    infer_instance
  have h : (strictDiagramTelescopeSeedMap Q η).app X =
      Telescope.toTail (fun i => ((strictDiagramIterate Q i).obj F).obj X)
        (fun i => (strictDiagramTransition Q η i).app X) ≫ e := by
    apply Telescope.hom_ext
    intros
    rfl
  rw [h]
  exact (Telescope.toTail_isStableEquivalence _ _).comp he

/-- The original telescope is stably mapped to its actual Bass image, in every signed degree. -/
theorem strictDiagramTelescopeSelfMap_isStableEquivalence (X : C) :
    IsStableEquivalence ((strictDiagramTelescopeSelfMap Q η).app X) :=
  (strictDiagramTelescopeSeedMap_isStableEquivalence Q η X).comp
    (strictDiagramTelescopeComparison_isStableEquivalence Q
      (fun i => (strictDiagramIterate Q i).obj F) (strictDiagramTransition Q η) X)

end Quillen.KTheory.Bass
