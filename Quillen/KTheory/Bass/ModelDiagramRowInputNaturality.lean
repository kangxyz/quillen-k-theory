/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.DiagramRowInputNaturality
public import Quillen.KTheory.Bass.ModelDiagramRowRefinementNaturality

/-!
# Actual Model transformations preserve every computed row refinement

The original Model row transposition is equivariant under exact Model maps.
The explicit cone/loop induction propagates this fact through every finite
Bass stage, giving genuine maps between the proper row targets.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.KTheory.Bass.ModelDiagramRowInterchange
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  {F G : C ⥤ Model.{w}} (η : F ⟶ G)

/-- Every computed finite row interchange preserves the original exact input map. -/
theorem stage_input_naturality (i : ℕ) (X : C) (k : ℕ)
    (x : (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space (k + 3)) :
    stage Q G i X k
        ((((strictDiagramIterate Q i).map
          (Functor.whiskerRight η prespectrumFunctor)).app X).map (k + 3) x) =
      (((strictDiagramIterate Q i).map
        (Functor.whiskerRight η prespectrumFunctor)).app X).map (k + 3)
          (stage Q F i X k x) := by
  unfold stage
  exact DiagramRowInterchange.iterate_input_naturality Q
      (initial F) (initial_point F) (initial_naturality F)
      (initial G) (initial_point G) (initial_naturality G)
      (Functor.whiskerRight η prespectrumFunctor)
      (fun X k x => RowHomotopyPushout.vertex_naturality k (η.app X) x) i X k x

/-- The actual unlooped cone map commutes with the computed original row interchange. -/
theorem cone_input_naturality (i : ℕ) (X : C) (k : ℕ)
    (x : (ModelDiagramRowRefinement.source Q i F X).space (k + 3)) :
    cone Q i G X k
        (((ConeTrack.map Q ((strictDiagramIterate Q i).map
          (Functor.whiskerRight η prespectrumFunctor))).app X).map (k + 3) x) =
      ((ConeTrack.map Q ((strictDiagramIterate Q i).map
        (Functor.whiskerRight η prespectrumFunctor))).app X).map (k + 3)
          (cone Q i F X k x) :=
  DiagramRowInterchange.cone_input_naturality Q
    (stage Q F i) (stage_point Q F i) (stage_naturality Q F i)
    (stage Q G i) (stage_point Q G i) (stage_naturality Q G i)
    ((strictDiagramIterate Q i).map (Functor.whiskerRight η prespectrumFunctor))
    (stage_input_naturality Q η i) X k x

end Quillen.KTheory.Bass.ModelDiagramRowInterchange

namespace Quillen.KTheory.Bass.ModelDiagramRowRefinement
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) {F G : C ⥤ Model.{w}} (η : F ⟶ G)

/-- The unchanged original input transformation on finite unlooped cones. -/
def inputSourceMap : sourceDiagram Q i F ⟶ sourceDiagram Q i G :=
  ConeTrack.map Q ((strictDiagramIterate Q i).map (Functor.whiskerRight η prespectrumFunctor))

/-- The actual input transformation induces a map between computed proper row carriers. -/
def inputMap (X : C) : carrier Q i F X ⟶ carrier Q i G X :=
  RowRefinement.map (ModelDiagramRowInterchange.cone Q i F X)
    (ModelDiagramRowInterchange.cone Q i G X)
    (ModelDiagramRowInterchange.cone_point Q i F X)
    (ModelDiagramRowInterchange.cone_point Q i G X)
    ((inputSourceMap Q i η).app X)
    (ModelDiagramRowInterchange.cone_input_naturality Q η i X)

/-- The comparison square retains the actual input cone map and original row comparisons. -/
theorem comparison_input_naturality (X : C) :
    (inputSourceMap Q i η).app X ≫ comparison Q i G X =
      comparison Q i F X ≫ inputMap Q i η X :=
  RowRefinement.comparison_naturality
    (ModelDiagramRowInterchange.cone Q i F X) (ModelDiagramRowInterchange.cone Q i G X)
    (ModelDiagramRowInterchange.cone_point Q i F X)
    (ModelDiagramRowInterchange.cone_point Q i G X)
    ((inputSourceMap Q i η).app X)
    (ModelDiagramRowInterchange.cone_input_naturality Q η i X)
    (ModelDiagramRowInterchange.cone_structure Q i F X)
    (ModelDiagramRowInterchange.cone_structure Q i G X)

/-- Input maps form a natural transformation under every original coefficient arrow. -/
theorem inputMap_naturality {X Y : C} (f : X ⟶ Y) :
    (diagram Q i F).map f ≫ inputMap Q i η Y =
      inputMap Q i η X ≫ (diagram Q i G).map f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  cases n with
  | zero =>
    change Path (Path.refl ((source Q i F X).point 2))
      (Path.refl ((source Q i F X).point 2)) at γ
    apply Path.ext; funext r; apply Path.ext; funext s
    exact congrArg (fun a => a.map 2 (γ r s)) ((inputSourceMap Q i η).naturality f)
  | succ k =>
    change Path ((source Q i F X).point (k + 2)) ((source Q i F X).point (k + 2)) at γ
    apply Path.ext; funext s
    exact congrArg (fun a => a.map (k + 2) (γ s)) ((inputSourceMap Q i η).naturality f)

/-- The whole computed proper row diagrams retain the original exact Model transformation. -/
def inputNatTrans : diagram Q i F ⟶ diagram Q i G where
  app := inputMap Q i η
  naturality _ _ := inputMap_naturality Q i η

/-- Original comparisons are natural in both the input Model diagram and its coefficients. -/
theorem comparisonNatTrans_input :
    inputSourceMap Q i η ≫ comparisonNatTrans Q i G =
      comparisonNatTrans Q i F ≫ inputNatTrans Q i η := by
  ext X
  exact comparison_input_naturality Q i η X

end Quillen.KTheory.Bass.ModelDiagramRowRefinement
