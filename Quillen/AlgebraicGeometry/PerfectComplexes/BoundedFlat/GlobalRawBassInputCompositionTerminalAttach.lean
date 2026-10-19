/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionCarrierCharts
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCompactAttachment
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCompactPrecompAttachment
public import Quillen.Topology.Path.ScalarRectangleConcatenation

/-!
# Original whole input surfaces inside the terminal composition face

The original thirty-one-node input surfaces are attached by actual Laurent postcomposition
and base precomposition. Both full source anchors use the chosen geometric composition
isomorphisms. These are whole native pieces; their carrier seams are not asserted here.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTerminalAttach

/-- The unchanged normalized model morphism of an actual scheme arrow. -/
def arrow {V W : Scheme.{u}} (h : V ⟶ W) :
    modelOf (boundedFlatPerfectWaldhausen W) ⟶ modelOf (boundedFlatPerfectWaldhausen V) :=
  modelMap _ _ (boundedFlatNormalizedPullback_exact h) (boundedFlatNormalizedPullback_obj_zero _)

/-- The whole original input surface, before either actual attachment. -/
def originalFace {V W : Scheme.{u}} (h : V ⟶ W) :
    C(unitInterval × unitInterval, |nerve (Codiscrete (InputDescSimplex.Node h))|) :=
  (CommonReferenceNerve.parameter (InputDescSimplex.reference h) (InputDescSimplex.nodes h)).comp
    BassH0Diagram.parameter

/-- Every point of the original input surface keeps its selected native comparison. -/
theorem original_native {V W : Scheme.{u}} (h : V ⟶ W) (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen W)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputDescSimplex.reference h)
      (originalFace h) n ((s, t), x) =
      (inputComparisonHomotopy h).level n
        (s, HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app W))
          (boundedFlatPerfectPrespectrumMap (projection.app W)) n (t, x)) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
    (InputDescSimplex.reference h) (originalFace h) (InputDescSimplex.nodes h) (s, t)
    (BassH0Diagram.parameter (s, t)) rfl n x).trans ?_
  rw [CommonReferenceNerve.prespectrumFamily_eq]
  exact InputDescSimplex.cylinder_native h n s t x

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Actual Laurent functor composition is the total equality of the first attachment. -/
theorem post_total :
    laurent.map f ≫ (laurent.map g ≫ laurentProjection.app Z) =
      laurent.map (f ≫ g) ≫ laurentProjection.app Z := by
  rw [← Category.assoc, ← laurent.map_comp f g]

/-- The original geometric composition iso supplies the complete postcomposition anchor. -/
def postAnchor : (InputCompositionCarrierCharts.source f g).functor ≅
    (InputDescSimplex.reference g ≫ arrow (laurent.map f)).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedFlatNormalizedPullback (post_total f g).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (laurent.map f)
        (laurent.map g ≫ laurentProjection.app Z)) AsSmall.up)

/-- All complete original H(g) nodes carry their actual Laurent postcomposition reference. -/
def postNode := CommonReferenceNerve.attachPostcompNode (InputDescSimplex.reference g)
  (arrow (laurent.map f)) (InputCompositionCarrierCharts.source f g) (postAnchor f g)

/-- The entire original postcomposed first comparison half, with both independent clocks. -/
def postFace : C(unitInterval × unitInterval, InputCompositionCarrierCharts.Carrier f g) :=
  (CommonReferenceNerve.mapParameter (postNode f g)).comp (originalFace g)

/-- Whole native postcomposition preserves every original input-comparison value. -/
theorem post_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (postFace f g) n ((s, t), x) =
      (boundedFlatPerfectPrespectrumMap (laurent.map f)).map n
        ((inputComparisonHomotopy g).level n
          (s, HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app Z))
            (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (t, x))) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_attachPostcomp
    (InputDescSimplex.reference g) (arrow (laurent.map f))
    (InputCompositionCarrierCharts.source f g) (postAnchor f g) (originalFace g)
    n (s, t) x).trans ?_
  exact congrArg ((boundedFlatPerfectPrespectrumMap (laurent.map f)).map n)
    (original_native g n s t x)

/-- The whole first comparison half is literally the prescribed terminal H1 face. -/
theorem post_cell (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (postFace f g) n ((s, t), x) =
      (InputCompositionCharts.compositeComparison f g).level n
        (Quillen.NativePathCells.lower s,
          HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app Z))
            (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (t, x)) := by
  refine (post_native f g n s t x).trans ?_
  symm
  exact Quillen.ScalarRectangle.homotopy_lower _ _ s _

/-- Original Laurent naturality identifies the middle attachment total. -/
theorem pre_total :
    (laurent.map f ≫ laurentProjection.app Y) ≫ g =
      laurent.map (f ≫ g) ≫ laurentProjection.app Z := by
  have hg : laurent.map g ≫ laurentProjection.app Z = laurentProjection.app Y ≫ g :=
    laurentProjection.naturality g
  rw [Category.assoc, ← hg, ← Category.assoc, ← laurent.map_comp f g]

/-- The middle attachment retains the actual base-arrow composition iso and total equality. -/
def preAnchor : (InputCompositionCarrierCharts.source f g).functor ≅
    (arrow g ≫ InputDescSimplex.reference f).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedFlatNormalizedPullback (pre_total f g).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (laurent.map f ≫ laurentProjection.app Y) g)
    AsSmall.up)

/-- Every complete H(f) node retains the actual normalized base premap and reference. -/
def preNode := CommonReferenceNerve.attachPrecompNode (InputDescSimplex.reference f)
  (arrow g) (InputCompositionCarrierCharts.source f g) (preAnchor f g)

/-- The original middle surface of the second comparison half. -/
def preFace : C(unitInterval × unitInterval, InputCompositionCarrierCharts.Carrier f g) :=
  (CommonReferenceNerve.mapParameter (preNode f g)).comp (originalFace f)

/-- Whole native precomposition retains the unchanged input surface at every native point. -/
theorem pre_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (preFace f g) n ((s, t), x) =
      (inputComparisonHomotopy f).level n
        (s, HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app Y))
          (boundedFlatPerfectPrespectrumMap (projection.app Y)) n
            (t, (boundedFlatPerfectPrespectrumMap g).map n x)) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_attachPrecomp
    (InputDescSimplex.reference f) (arrow g) (InputCompositionCarrierCharts.source f g)
    (preAnchor f g) (originalFace f) n (s, t) x).trans ?_
  exact original_native f n s t ((boundedFlatPerfectPrespectrumMap g).map n x)

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTerminalAttach
