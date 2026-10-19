/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedUnitNodes
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputRawSquareProduct

/-!
# The original strict-unit input to the Laurent evaluation comparison

The first product factor is the strict source unit and the second is the original Laurent
input evaluation. Their original operation order is retained. The public coordinates are
comparison time and unit time, while the actual product receives unit time first.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.SimplexParameters
open Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedInputUnitProduct
open GlobalSectionChangeIndex InputNormalizationPrism CommonReferenceNerve

/-- The unchanged strict source Laurent projection is the first product factor. -/
def unitMap (Y : Scheme.{u}) := globalModel.map (GlobalRawBass.laurentProjection.app Y).op

/-- The original strict forward unit, before any evaluation comparison. -/
def unitIso (Y : Scheme.{u}) : (unitMap Y).functor ≅ (unitMap Y).functor :=
  onFunctor (unitMap Y).functor (GlobalSchemeLaurentTrack.unit (op Y))

/-- The two strict-unit vertices have the same actual Model arrow and distinct references. -/
def unitVertices (Y : Scheme.{u}) : Fin 2 →
    (globalModel.obj (op Y) ⟶ globalModel.obj (op (laurent.obj Y))) := fun _ ↦ unitMap Y

/-- The full original source unit reference. -/
def unitAnchors (Y : Scheme.{u}) : ∀ i, (unitMap Y).functor ≅ (unitVertices Y i).functor :=
  ![Iso.refl _, unitIso Y]

/-- The original strict Laurent unit as its actual two-node simplex. -/
def unitSimplex (Y : Scheme.{u}) :=
  ModelSimplex.ofIsos (unitMap Y) (unitVertices Y) (unitAnchors Y)

private def unitTriangleFace : ⦋2⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 1], by decide⟩

private theorem unit_triangle (Y : Scheme.{u}) :
    HomotopyLift (unitSimplex Y) (triangle unitTriangleFace)
      (prespectrumTransformationCompositionHomotopy
        (F := unitMap Y) (G := unitMap Y) (H := unitMap Y) (unitIso Y).hom (𝟙 _)
        (fun _ ↦ (globalModel.obj (op (laurent.obj Y))).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (globalModel.obj (op (laurent.obj Y))).waldhausen.weq_iso _ inferInstance)) := by
  apply triangle_lift
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact Category.comp_id _

/-- The whole source-unit edge is the unchanged strict Laurent track. -/
theorem unit_native (Y : Scheme.{u}) :
    PathLift (unitSimplex Y) (edge (k := 1) 0 1)
      (GlobalSchemeLaurentTrack.homotopy (op Y)) := by
  have h := PathLift.trans_left _ (HomotopyLift.target _ (unit_triangle Y))
  intro n s x
  exact h n s x

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Strict source composition identifies the actual first product reference. -/
theorem source_eq : (InputSeedCarrier.laurentRef g).functor =
    (unitMap Y ≫ firstSource (laurent.map g)).functor :=
  (congrArg (fun F ↦ F ⋙ (evaluationModel (op (laurent.obj X))).functor)
    (globalReindex_comp (laurent.map g) (GlobalRawBass.laurentProjection.app Y))).trans
      (Functor.assoc (unitMap Y).functor (globalModel.map (laurent.map g).op).functor
        (evaluationModel (op (laurent.obj X))).functor)

/-- The full original strict-composition reference, before either scalar time. -/
def anchor : (InputSeedCarrier.laurentRef g).functor ≅
    (unitMap Y ≫ firstSource (laurent.map g)).functor := eqToIso (source_eq g)

/-- Four original product nodes, ordered by strict-unit factor then evaluation factor. -/
def nodes (i : Fin 4) : Node (InputSeedCarrier.laurentRef g) :=
  ⟨CommonReferenceProduct.vertices (unitVertices Y) (firstVertices (laurent.map g)) i,
    anchor g ≪≫ CommonReferenceProduct.references (unitMap Y) (unitVertices Y) (unitAnchors Y)
      (firstSource (laurent.map g)) (firstVertices (laurent.map g))
      (firstAnchors (laurent.map g)) i⟩

/-- Comparison time is first in the interface; original strict-unit action occurs first. -/
def scalar : C(I × I, StdSimplex ℝ (Fin 4)) :=
  ⟨fun z ↦ Quillen.SimplexGrid.parameter.{u} 1 1
    ((edge (k := 1) 0 1) z.2, (edge (k := 1) 0 1) z.1), by fun_prop⟩

/-- The actual two-time product in the unchanged mixed Laurent reference. -/
def parameter : C(I × I, |nerve (Codiscrete (Node (InputSeedCarrier.laurentRef g)))|) :=
  (CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (nodes g)).comp scalar.{u+1}

private theorem simplex_eq :
    ModelSimplex.ofIsos (InputSeedCarrier.laurentRef g)
      (fun i ↦ (nodes g i).1) (fun i ↦ (nodes g i).2) =
    CommonReferenceProduct.simplex (unitMap Y) (unitVertices Y) (unitAnchors Y)
      (firstSource (laurent.map g)) (firstVertices (laurent.map g))
      (firstAnchors (laurent.map g)) :=
  ModelSimplex.ofIsos_change_reference (anchor g) _ _

/-- Every native product point is original Laurent evaluation on the original strict unit. -/
theorem native (n : ℕ) (r s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    prespectrumFamily (InputSeedCarrier.laurentRef g) (nodes g) n (scalar.{u+1} (r, s), x) =
      (evaluationComparison (laurent.map g)).level n
        (r, (GlobalSchemeLaurentTrack.homotopy (op Y)).level n (s, x)) := by
  rw [prespectrumFamily_eq, simplex_eq]
  exact (CommonReferenceProduct.prespectrum_comp
    (unitMap Y) (unitVertices Y) (unitAnchors Y)
    (firstSource (laurent.map g)) (firstVertices (laurent.map g))
    (firstAnchors (laurent.map g)) n x
    ((edge (k := 1) 0 1) s) ((edge (k := 1) 0 1) r)).trans
      ((congrArg (fun y ↦ prespectrumSimplexFamily (firstSimplex (laurent.map g)) n
        ((edge (k := 1) 0 1) r, y)) (unit_native Y n s x)).trans
          (first_native (laurent.map g) n r
            ((GlobalSchemeLaurentTrack.homotopy (op Y)).level n (s, x))))

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedInputUnitProduct
