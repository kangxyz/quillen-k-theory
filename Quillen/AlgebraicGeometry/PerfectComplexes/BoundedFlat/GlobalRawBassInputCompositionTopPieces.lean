/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionCarrierCharts
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityProjection
public import Quillen.Waldhausen.SConstruction.Iterated.RealizationSimplexComposition
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveWhiskering
public import Quillen.Topology.Prespectrum.NativeMovingSquareCells

/-!
# Original pieces of the span-composition vertex face

Both original polynomial moving squares and the independent base-composition/Bass-path
product have complete geometric reference carriers and whole native recovery. They are only
the three pieces of the first vertex stage; no glued top face or reassociation stage is claimed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTopPieces

private theorem post_family {V W T : Model.{u}} {k : ℕ}
    (F : V ⟶ T) (G : V ⟶ W) (J : W ⟶ T) (δ : F.functor ≅ (G ≫ J).functor)
    (N : Fin (k + 1) → CommonReferenceNerve.Node G) :
    ModelSimplex.ofIsos F (fun i ↦ (N i).1 ≫ J)
        (fun i ↦ δ ≪≫ isoWhiskerRight (N i).2 J.functor) =
      (ModelSimplex.ofIsos G (fun i ↦ (N i).1) (fun i ↦ (N i).2)).postcomp J := by
  rw [ModelSimplex.ofIsos_change_reference]
  exact (ModelSimplex.ofIsos_postcomp _ _ _ _).symm

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The genuine geometric source of the original polynomial composition rectangle. -/
abbrev polynomialSource := NormalizedTripleSimplex.sourceMap (projection.app X) f g

/-- All original polynomial rectangle nodes and their complete source references. -/
abbrev polynomialNodes := DoubleSquareMergedSimplex.nodes
  g f (polynomial.map g) (polynomial.map f)
  (projection.app Z) (projection.app Y) (projection.app X)
  (projection.naturality g).symm (projection.naturality f).symm

/-- The original polynomial rectangle simplex on the literal three scheme projections. -/
def polynomialSimplex := DoubleSquareMergedSimplex.simplex
  g f (polynomial.map g) (polynomial.map f)
  (projection.app Z) (projection.app Y) (projection.app X)
  (projection.naturality g).symm (projection.naturality f).symm

private theorem polynomial_rectangle_lift :
    HomotopyLift (polynomialSimplex f g) DoubleSquareScalarPaths.rectangleParameter
      (InputCompositionPolynomial.rectangle f g) :=
  DoubleSquareScalarPaths.original_rectangle_nativeLift
    g f (polynomial.map g) (polynomial.map f)
    (projection.app Z) (projection.app Y) (projection.app X)
    (projection.naturality g).symm (projection.naturality f).symm

private theorem polynomial_comparison_lift :
    HomotopyLift (polynomialSimplex f g)
      DoubleSquareScalarPaths.originalComparisonParameter
      (InputCompositionPolynomial.comparison f g) := by
  intro n r s x
  exact (HomotopyLift.symmPath _
    (polynomial_rectangle_lift f g)) n r s x

private theorem polynomial_target_path :
    PathLift (polynomialSimplex f g)
      DoubleSquareScalarPaths.targetChart (InputCompositionPolynomial.targetTrack f g) := by
  let S := polynomialSimplex f g
  have h := HomotopyLift.target S (polynomial_comparison_lift f g)
  have h' := PathLift.trans_left S h
  intro n t x
  have hv := (PathLift.trans_left S h') n (unitInterval.symm t) x
  change prespectrumSimplexFamily S n
      (DoubleSquareScalarPaths.targetChart (unitInterval.symm (unitInterval.symm t)), x) =
    (InputCompositionPolynomial.targetTrack f g).level n
      (unitInterval.symm (unitInterval.symm t), x) at hv
  rw [unitInterval.symm_symm] at hv
  exact hv

private theorem polynomial_source_path :
    PathLift (polynomialSimplex f g)
      DoubleSquareScalarPaths.sourceChart (InputCompositionPolynomial.sourceTrack f g) := by
  let S := polynomialSimplex f g
  exact PathLift.trans_right S (HomotopyLift.target S (polynomial_comparison_lift f g))

private theorem polynomial_outer_path :
    PathLift (polynomialSimplex f g)
      DoubleSquareScalarPaths.outerSquarePath (polynomialSquareHomotopy (f ≫ g)) := by
  let S := polynomialSimplex f g
  exact PathLift.trans_right S
    (PathLift.trans_left S (HomotopyLift.target S (polynomial_comparison_lift f g)))

private theorem polynomial_boundary_lift :
    HomotopyLift (polynomialSimplex f g)
      DoubleSquareScalarPaths.coefficientBoundaryParameter
      (InputCompositionPolynomial.boundary f g) :=
  HomotopyLift.boundaryOfComparison (polynomialSimplex f g)
    (polynomial_target_path f g) (polynomial_outer_path f g) (polynomial_source_path f g)
    (polynomial_comparison_lift f g)

/-- The original scalar boundary word recovers the frozen polynomial Square at every point. -/
theorem polynomial_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    prespectrumSimplexFamily (polynomialSimplex f g) n
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, s), x) =
      (InputCompositionPolynomial.square f g).level n (r, (s, x)) :=
  HomotopyLift.toSquare _ (polynomial_boundary_lift f g) n r s x

variable (k : laurent ⟶ polynomial)
  (hk : ∀ V, k.app V ≫ projection.app V = laurentProjection.app V)

/-- The actual normalized model map of the positive or inverse target chart. -/
def chartMap : modelOf (boundedFlatPerfectWaldhausen (polynomial.obj X)) ⟶
    modelOf (boundedFlatPerfectWaldhausen (laurent.obj X)) :=
  modelMap _ _ (boundedFlatNormalizedPullback_exact (k.app X))
    (boundedFlatNormalizedPullback_obj_zero _)

include hk in
/-- Both original target charts have the same actual geometric total after the source arrows. -/
theorem moving_total :
    k.app X ≫ (projection.app X ≫ f ≫ g) =
      laurent.map (f ≫ g) ≫ laurentProjection.app Z := by
  have hL : laurent.map (f ≫ g) ≫ laurentProjection.app Z =
      laurentProjection.app X ≫ (f ≫ g) := laurentProjection.naturality (f ≫ g)
  rw [← Category.assoc (k.app X) (projection.app X), hk X]
  exact hL.symm

/-- The actual chart composition iso anchors the polynomial surface at the unchanged H0 source. -/
def movingAnchor : (InputCompositionCarrierCharts.source f g).functor ≅
    (polynomialSource f g ≫ chartMap (X := X) k).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedFlatNormalizedPullback (moving_total f g k hk).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (k.app X) (projection.app X ≫ f ≫ g)) AsSmall.up)

/-- Every postcomposed polynomial node retains its full actual common-reference anchor. -/
def movingNodes (i : Fin 18) : InputCompositionCarrierCharts.Node f g :=
  ⟨(polynomialNodes f g i).1 ≫ chartMap (X := X) k,
    movingAnchor f g k hk ≪≫
      isoWhiskerRight (polynomialNodes f g i).2 (chartMap (X := X) k).functor⟩

/-- The whole anchored chart family is the actual original polynomial surface postcomposition. -/
theorem moving_family :
    ModelSimplex.ofIsos (InputCompositionCarrierCharts.source f g)
      (fun i ↦ (movingNodes f g k hk i).1) (fun i ↦ (movingNodes f g k hk i).2) =
      (polynomialSimplex f g).postcomp (chartMap (X := X) k) :=
  post_family (InputCompositionCarrierCharts.source f g) (polynomialSource f g)
    (chartMap (X := X) k) (movingAnchor f g k hk) (polynomialNodes f g)

/-- The moving piece retains the entire original two-coordinate polynomial square clock. -/
def movingFace : C(unitInterval × unitInterval, InputCompositionCarrierCharts.Carrier f g) :=
  (CommonReferenceNerve.parameter (InputCompositionCarrierCharts.source f g)
    (movingNodes f g k hk)).comp DoubleSquareScalarPaths.coefficientMovingSquareParameter

/-- Every moving-piece value is the original polynomial Square followed by the actual chart. -/
theorem movingFace_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (movingFace f g k hk) n ((r, s), x) =
      (boundedFlatPerfectPrespectrumMap (k.app X)).map n
        ((InputCompositionPolynomial.square f g).level n (r, (s, x))) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
    (InputCompositionCarrierCharts.source f g) (movingFace f g k hk)
    (movingNodes f g k hk) (r, s)
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, s)) rfl n x).trans ?_
  rw [CommonReferenceNerve.prespectrumFamily_eq, moving_family]
  refine (prespectrumSimplexFamily_postcomp
    (polynomialSimplex f g) (chartMap (X := X) k) n
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, s)) x).trans ?_
  exact congrArg (fun y ↦ (boundedFlatPerfectPrespectrumMap (k.app X)).map n y)
    (polynomial_native f g n r s x)

/-- The original base-composition source of the middle product. -/
abbrev baseSource := BinaryNormalizationSimplex.sourceMap f g

/-- All three original base-composition vertices, including the geometric intermediate. -/
def baseVertices : Fin 3 →
    (modelOf (boundedFlatPerfectWaldhausen Z) ⟶ modelOf (boundedFlatPerfectWaldhausen X)) :=
  ![baseSource f g, BinaryNormalizationSimplex.intermediateMap f g,
    BinaryNormalizationSimplex.targetMap f g]

/-- The original complete references of the split base-composition triangle. -/
def baseReferences : ∀ i, (baseSource f g).functor ≅ (baseVertices f g i).functor :=
  Fin.cases (Iso.refl _) (Fin.cases (BinaryNormalizationSimplex.first f g)
    (Fin.cases (BinaryNormalizationSimplex.total f g) (fun i ↦ Fin.elim0 i)))

/-- The genuine independent product source for base composition and the target Bass path. -/
abbrev middleSource := baseSource f g ≫ InputIdentityProjection.source X

/-- The original positive projection and Laurent naturality identify the product total. -/
theorem middle_total :
    (plus.app X ≫ projection.app X) ≫ (f ≫ g) =
      laurent.map (f ≫ g) ≫ laurentProjection.app Z := by
  rw [plus_projection X]
  exact (laurentProjection.naturality (f ≫ g)).symm

/-- The actual composition iso anchors the complete middle product at the same H0 source. -/
def middleAnchor : (InputCompositionCarrierCharts.source f g).functor ≅
    (middleSource f g).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedFlatNormalizedPullback (middle_total f g).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (plus.app X ≫ projection.app X) (f ≫ g)) AsSmall.up)

/-- Every original middle-product node retains the full product reference. -/
def middleProductNodes (i : Fin 15) : CommonReferenceNerve.Node (middleSource f g) :=
  ⟨CommonReferenceProduct.vertices (baseVertices f g)
      (fun j ↦ (InputIdentityProjection.nodes X j).1) i,
    CommonReferenceProduct.references (baseSource f g) (baseVertices f g) (baseReferences f g)
      (InputIdentityProjection.source X) (fun j ↦ (InputIdentityProjection.nodes X j).1)
      (fun j ↦ (InputIdentityProjection.nodes X j).2) i⟩

/-- The whole middle product occupies the identical source carrier as both moving pieces. -/
def middleNodes : Fin 15 → InputCompositionCarrierCharts.Node f g :=
  ModelSimplex.reanchorNodes (middleAnchor f g) (middleProductNodes f g)

/-- Reference change preserves the entire independent-parameter middle model simplex. -/
theorem middle_family :
    ModelSimplex.ofIsos (InputCompositionCarrierCharts.source f g)
      (fun i ↦ (middleNodes f g i).1) (fun i ↦ (middleNodes f g i).2) =
      CommonReferenceProduct.simplex (baseSource f g) (baseVertices f g) (baseReferences f g)
        (InputIdentityProjection.source X) (fun j ↦ (InputIdentityProjection.nodes X j).1)
        (fun j ↦ (InputIdentityProjection.nodes X j).2) :=
  ModelSimplex.ofIsos_change_reference (middleAnchor f g)
    (fun i ↦ (middleProductNodes f g i).1) (fun i ↦ (middleProductNodes f g i).2)

/-- Base-composition and original Bass height are the unchanged two product clocks. -/
def middleParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 15)) :=
  ⟨fun z ↦ Quillen.SimplexGrid.parameter.{u + 1} 2 4
    (binaryPath (k := 2) 0 1 2 z.1, InputIdentityProjection.parameter z.2), by fun_prop⟩

/-- The complete original middle product as a surface in the common actual reference carrier. -/
def middleFace : C(unitInterval × unitInterval, InputCompositionCarrierCharts.Carrier f g) :=
  (CommonReferenceNerve.parameter (InputCompositionCarrierCharts.source f g)
    (middleNodes f g)).comp middleParameter.{u}

/-- The full middle product evaluates to the original Bass path on original base composition. -/
theorem middleFace_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (middleFace f g) n ((r, t), x) =
      (squareHomotopy X).level n
        (t, (InputCompositionPolynomial.sourceComposition f g).level n (r, x)) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
    (InputCompositionCarrierCharts.source f g) (middleFace f g) (middleNodes f g) (r, t)
    (middleParameter.{u} (r, t)) rfl n x).trans ?_
  rw [CommonReferenceNerve.prespectrumFamily_eq, middle_family]
  refine (CommonReferenceProduct.prespectrum_comp (baseSource f g)
    (baseVertices f g) (baseReferences f g) (InputIdentityProjection.source X)
    (fun j ↦ (InputIdentityProjection.nodes X j).1)
    (fun j ↦ (InputIdentityProjection.nodes X j).2) n x
    (binaryPath (k := 2) 0 1 2 r) (InputIdentityProjection.parameter t)).trans ?_
  refine (InputIdentityProjection.native X n t _).trans ?_
  exact congrArg (fun y ↦ (squareHomotopy X).level n (t, y))
    (BinaryNormalizationSimplex.native_path f g n r x)

open Quillen.NativePathCells

/-- The complete positive piece is the actual first-half M cylinder at its original half clock. -/
theorem plus_top_cell (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (movingFace f g plus plus_projection) n ((r, t), x) =
      (InputCompositionCharts.spanTrack f g).level n
        (lower r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (lower t, x)) := by
  rw [movingFace_native]
  change (boundedFlatPerfectPrespectrumMap (plus.app X)).map n
      ((InputCompositionPolynomial.square f g).level n (r, (t, x))) =
    (comparison X).map n ((InputCompositionSpan.homotopy f g).level n (lower r, _))
  rw [InputCompositionSpan.homotopy_cylinder_lower]
  unfold InputCompositionSpan.movingSquare
  rw [HomotopyPushout.identicalMoving_lower]
  rfl

/-- The entire middle piece keeps the original independent M clock and middle-quarter height. -/
theorem middle_top_cell (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (middleFace f g) n ((r, t), x) =
      (InputCompositionCharts.spanTrack f g).level n
        (lower r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (upper (lower t), x)) := by
  rw [middleFace_native]
  change (squareHomotopy X).level n
      (t, (InputCompositionPolynomial.sourceComposition f g).level n (r, x)) =
    (comparison X).map n ((InputCompositionSpan.homotopy f g).level n (lower r, _))
  rw [InputCompositionSpan.homotopy_cylinder_lower]
  unfold InputCompositionSpan.movingSquare
  rw [HomotopyPushout.identicalMoving_middle]
  rfl

/-- The inverse piece retains the original reversed square and final-quarter M height. -/
theorem minus_top_cell (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (movingFace f g minus minus_projection) n ((r, unitInterval.symm t), x) =
      (InputCompositionCharts.spanTrack f g).level n
        (lower r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (upper (upper t), x)) := by
  rw [movingFace_native]
  change (boundedFlatPerfectPrespectrumMap (minus.app X)).map n
      ((InputCompositionPolynomial.square f g).level n (r, (unitInterval.symm t, x))) =
    (comparison X).map n ((InputCompositionSpan.homotopy f g).level n (lower r, _))
  rw [InputCompositionSpan.homotopy_cylinder_lower]
  unfold InputCompositionSpan.movingSquare
  rw [HomotopyPushout.identicalMoving_upper]
  rfl

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTopPieces
