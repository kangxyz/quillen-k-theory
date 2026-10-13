/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.TelescopePushoutIso
public import Quillen.Topology.Prespectrum.TelescopeConeIso
public import Quillen.Topology.Prespectrum.TelescopeDiagram
public import Quillen.Topology.Prespectrum.StrictSquareCone

/-!
# Original strict-square comparison and telescope interchange

For a sequence of actual strict coefficient diagrams, the unchanged square span commutes with
the original telescope. The resulting iso preserves the literal square-comparison arrow,
including its original constant overlap track, so the actual square cones commute as well.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u v w
namespace Quillen.LoopPrespectrum.Telescope
variable {C : Type u} [Category.{v} C]
    (F : ℕ → C ⥤ LoopPrespectrum.{w}) (τ : ∀ i, F i ⟶ F (i + 1))
    (S : Arrow (Arrow C))

/-- The original natural transformation acts on all four corners of the actual square. -/
def diagramSquareTransition (i : ℕ) :
    (F i).mapArrow.mapArrow.obj S ⟶ (F (i + 1)).mapArrow.mapArrow.obj S :=
  ((Functor.mapArrowFunctor (Arrow C) (Arrow LoopPrespectrum)).map
    ((Functor.mapArrowFunctor C LoopPrespectrum).map (τ i))).app S

/-- The unchanged original span transition, with its whole reduced double cylinder. -/
def diagramSpanTransition (i : ℕ) : StrictSquare.span ((F i).mapArrow.mapArrow.obj S) ⟶
    StrictSquare.span ((F (i + 1)).mapArrow.mapArrow.obj S) :=
  StrictSquare.spanMap (diagramSquareTransition F τ S i)

/-- The actual pushout interchange specializes to the original coefficient-square span. -/
def diagramSpanIso : StrictSquare.span ((diagramFunctor F τ).mapArrow.mapArrow.obj S) ≅
    prespectrum (fun i => StrictSquare.span ((F i).mapArrow.mapArrow.obj S))
      (diagramSpanTransition F τ S) :=
  pushoutIso (fun i => (F i).obj S.left.left) (fun i => (τ i).app S.left.left)
    (fun i => (F i).obj S.left.right) (fun i => (τ i).app S.left.right)
    (fun i => (F i).obj S.right.left) (fun i => (τ i).app S.right.left)
    (fun i => (F i).map S.left.hom) (fun i => (F i).map S.hom.left)
    (fun i => (τ i).naturality S.left.hom) (fun i => (τ i).naturality S.hom.left)

/-- The original square comparisons strictly commute with the original stage transitions. -/
theorem diagramComparisonCompatibility (i : ℕ) :
    StrictSquare.comparison ((F i).mapArrow.mapArrow.obj S) ≫ (τ i).app S.right.right =
      diagramSpanTransition F τ S i ≫
        StrictSquare.comparison ((F (i + 1)).mapArrow.mapArrow.obj S) :=
  (StrictSquare.comparison_naturality (diagramSquareTransition F τ S i)).symm

/-- The telescope of the unchanged original square-comparison arrows. -/
def diagramComparisonMap :
    prespectrum (fun i => StrictSquare.span ((F i).mapArrow.mapArrow.obj S))
        (diagramSpanTransition F τ S) ⟶ (diagramFunctor F τ).obj S.right.right :=
  map (fun i => StrictSquare.span ((F i).mapArrow.mapArrow.obj S))
    (diagramSpanTransition F τ S)
    (fun i => (F i).obj S.right.right) (fun i => (τ i).app S.right.right)
    (fun i => StrictSquare.comparison ((F i).mapArrow.mapArrow.obj S))
    (diagramComparisonCompatibility F τ S)

/-- The interchange preserves the exact original square comparison, on the whole cylinder. -/
theorem diagramSpanIso_comparison :
    (diagramSpanIso F τ S).hom ≫ diagramComparisonMap F τ S =
      StrictSquare.comparison ((diagramFunctor F τ).mapArrow.mapArrow.obj S) := by
  apply HomotopyPushout.hom_ext
  · apply hom_ext; intros; rfl
  · apply hom_ext; intros; rfl
  · intro k s q
    induction q using Quot.inductionOn with
    | h z => rfl

/-- The actual span iso and unchanged final corner give an iso of the original comparison arrows. -/
def diagramComparisonIso :
    Arrow.mk (StrictSquare.comparison ((diagramFunctor F τ).mapArrow.mapArrow.obj S)) ≅
      Arrow.mk (diagramComparisonMap F τ S) :=
  Arrow.isoMk (diagramSpanIso F τ S) (Iso.refl _) (by
    exact (diagramSpanIso_comparison F τ S).trans (Category.comp_id _).symm)

/-- The original stage square cones and their exact original strict transitions. -/
def diagramConeTransition (i : ℕ) :
    mappingCone (StrictSquare.comparison ((F i).mapArrow.mapArrow.obj S)) ⟶
      mappingCone (StrictSquare.comparison ((F (i + 1)).mapArrow.mapArrow.obj S)) :=
  mappingConeMap (strictSquareComparisonFunctor.map (diagramSquareTransition F τ S i))

/-- The unchanged comparison cones commute with the original telescope by an actual iso. -/
def diagramConeIso :
    mappingCone (StrictSquare.comparison ((diagramFunctor F τ).mapArrow.mapArrow.obj S)) ≅
      prespectrum (fun i => mappingCone (StrictSquare.comparison ((F i).mapArrow.mapArrow.obj S)))
        (diagramConeTransition F τ S) :=
  mappingConeFunctor.mapIso (diagramComparisonIso F τ S) ≪≫
    coneIso (fun i => StrictSquare.span ((F i).mapArrow.mapArrow.obj S))
      (diagramSpanTransition F τ S)
      (fun i => (F i).obj S.right.right) (fun i => (τ i).app S.right.right)
      (fun i => StrictSquare.comparison ((F i).mapArrow.mapArrow.obj S))
      (diagramComparisonCompatibility F τ S)

/-- The inverse cone interchange keeps the actual final-corner height and inclusion. -/
theorem diagramConeIso_inv_target (k i : ℕ) (t : unitInterval)
    (y : ((F i).obj S.right.right).space k) :
    (diagramConeIso F τ S).inv.map k
      (cylinder
        (fun i => mappingCone (StrictSquare.comparison ((F i).mapArrow.mapArrow.obj S)))
        (diagramConeTransition F τ S) k i
        (t, (mappingConeInclusion
          (StrictSquare.comparison ((F i).mapArrow.mapArrow.obj S))).map k y)) =
      (mappingConeInclusion
        (StrictSquare.comparison ((diagramFunctor F τ).mapArrow.mapArrow.obj S))).map k
        (cylinder (fun i => (F i).obj S.right.right) (fun i => (τ i).app S.right.right) k i
          (t, y)) := rfl

/-- The inverse cone interchange retains independent cone time and original telescope height. -/
theorem diagramConeIso_inv_cylinder (k i : ℕ) (s t : unitInterval)
    (x : (StrictSquare.span ((F i).mapArrow.mapArrow.obj S)).space k) :
    (diagramConeIso F τ S).inv.map k
      (cylinder
        (fun i => mappingCone (StrictSquare.comparison ((F i).mapArrow.mapArrow.obj S)))
        (diagramConeTransition F τ S) k i
        (t, ReducedMappingCone.cylinder
          ((StrictSquare.span ((F i).mapArrow.mapArrow.obj S)).point k)
          (((F i).obj S.right.right).point k)
          ((StrictSquare.comparison ((F i).mapArrow.mapArrow.obj S)).map k) (s, x))) =
      ReducedMappingCone.cylinder
        ((StrictSquare.span ((diagramFunctor F τ).mapArrow.mapArrow.obj S)).point k)
        (((diagramFunctor F τ).obj S.right.right).point k)
        ((StrictSquare.comparison ((diagramFunctor F τ).mapArrow.mapArrow.obj S)).map k)
        (s, (diagramSpanIso F τ S).inv.map k
          (cylinder (fun i => StrictSquare.span ((F i).mapArrow.mapArrow.obj S))
            (diagramSpanTransition F τ S) k i (t, x))) := rfl

end Quillen.LoopPrespectrum.Telescope
