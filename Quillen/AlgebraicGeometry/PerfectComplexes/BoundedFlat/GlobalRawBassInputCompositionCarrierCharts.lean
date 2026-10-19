/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionChartNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputDescNative
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCubeExtension

/-!
# Three original composition faces in one geometric reference carrier

The direct input surface keeps its actual thirty-one dependent nodes. The positive and inverse
composition charts use their original eighteen nodes, precomposed with the actual polynomial
projection and anchored by its geometric composition isomorphism. All three whole native faces
have the same actual reference source. No edge identifications or cube are asserted here.
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
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionCarrierCharts

private theorem pre_family {V W T : Model.{u}} {k : ℕ}
    (F : V ⟶ T) (J : V ⟶ W) (G : W ⟶ T) (δ : F.functor ≅ (J ≫ G).functor)
    (N : Fin (k + 1) → CommonReferenceNerve.Node G) :
    ModelSimplex.ofIsos F (fun i ↦ J ≫ (N i).1)
        (fun i ↦ δ ≪≫ isoWhiskerLeft J.functor (N i).2) =
      (ModelSimplex.ofIsos G (fun i ↦ (N i).1) (fun i ↦ (N i).2)).precomp J := by
  rw [ModelSimplex.ofIsos_change_reference]
  exact (ModelSimplex.ofIsos_precomp _ _ _ _).symm

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The original direct input reference is retained, including its actual functor map cast. -/
abbrev source := InputDescSimplex.reference (f ≫ g)

/-- Complete geometric nodes and their original specified reference isomorphisms. -/
abbrev Node := CommonReferenceNerve.Node (source f g)

/-- The common carrier is the actual nerve of these full dependent nodes. -/
abbrev Carrier := |nerve (Codiscrete (Node f g))|

/-- The whole direct face uses exactly the original thirty-one-node input parameter. -/
def inputFace : C(unitInterval × unitInterval, Carrier f g) :=
  (CommonReferenceNerve.parameter (source f g) (InputDescSimplex.nodes (f ≫ g))).comp
    BassH0Diagram.parameter

/-- Every original direct face value survives at its unchanged native coordinates. -/
theorem inputFace_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (source f g) (inputFace f g) n ((s, t), x) =
      (inputComparisonHomotopy (f ≫ g)).level n
        (s, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (t, x)) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex (source f g)
    (inputFace f g) (InputDescSimplex.nodes (f ≫ g)) (s, t)
    (BassH0Diagram.parameter (s, t)) rfl n x).trans ?_
  rw [CommonReferenceNerve.prespectrumFamily_eq]
  exact InputDescSimplex.cylinder_native (f ≫ g) n s t x

/-- The actual normalized model map for the unchanged source polynomial projection. -/
def projectionMap : modelOf (boundedFlatPerfectWaldhausen Z) ⟶
    modelOf (boundedFlatPerfectWaldhausen (polynomial.obj Z)) :=
  modelMap _ _ (boundedFlatNormalizedPullback_exact (projection.app Z))
    (boundedFlatNormalizedPullback_obj_zero _)

variable (k : laurent ⟶ polynomial)
  (hk : ∀ V, k.app V ≫ projection.app V = laurentProjection.app V)

/-- The exact chart rectangle reference, before polynomial precomposition. -/
abbrev chartReference :=
  NormalizedTripleSimplex.sourceMap (k.app X) (polynomial.map f) (polynomial.map g)

include hk in
/-- Original projection naturality identifies the geometric total of either chart. -/
theorem chart_total :
    (k.app X ≫ polynomial.map f ≫ polynomial.map g) ≫ projection.app Z =
      laurent.map (f ≫ g) ≫ laurentProjection.app Z := by
  have hf : polynomial.map f ≫ projection.app Y = projection.app X ≫ f :=
    projection.naturality f
  have hg : polynomial.map g ≫ projection.app Z = projection.app Y ≫ g :=
    projection.naturality g
  have hL : laurent.map (f ≫ g) ≫ laurentProjection.app Z =
      laurentProjection.app X ≫ (f ≫ g) := laurentProjection.naturality (f ≫ g)
  simp only [Category.assoc]
  rw [hg, ← Category.assoc _ _ g, hf]
  simp only [Category.assoc]
  rw [← Category.assoc (k.app X) (projection.app X), hk X]
  exact hL.symm

/-- The chart reference is anchored by the actual total equality and original composition iso. -/
def chartReferenceIso : (source f g).functor ≅
    (projectionMap (Z := Z) ≫ chartReference f g k).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedFlatNormalizedPullback (chart_total f g k hk).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso
        (k.app X ≫ polynomial.map f ≫ polynomial.map g) (projection.app Z)) AsSmall.up)

/-- All eighteen original chart nodes retain their entire polynomial-precomposition anchor. -/
def chartNodes (i : Fin 18) : Node f g :=
  let N := DoubleSquareMergedSimplex.nodes
    (polynomial.map g) (polynomial.map f) (laurent.map g) (laurent.map f)
    (k.app Z) (k.app Y) (k.app X) (k.naturality g).symm (k.naturality f).symm i
  ⟨projectionMap (Z := Z) ≫ N.1,
    chartReferenceIso f g k hk ≪≫ isoWhiskerLeft (projectionMap (Z := Z)).functor N.2⟩

/-- The full anchored simplex is the original geometric chart simplex under its actual premap. -/
theorem chart_family :
    ModelSimplex.ofIsos (source f g) (fun i ↦ (chartNodes f g k hk i).1)
      (fun i ↦ (chartNodes f g k hk i).2) =
        (InputCompositionChartNative.simplex k f g).precomp (projectionMap (Z := Z)) :=
  pre_family (source f g) (projectionMap (Z := Z)) (chartReference f g k)
    (chartReferenceIso f g k hk)
    (DoubleSquareMergedSimplex.nodes
      (polynomial.map g) (polynomial.map f) (laurent.map g) (laurent.map f)
      (k.app Z) (k.app Y) (k.app X) (k.naturality g).symm (k.naturality f).symm)

/-- The complete chart uses its prescribed paused clock, with no scalar reparameterization. -/
def chartFace : C(unitInterval × unitInterval, Carrier f g) :=
  (CommonReferenceNerve.parameter (source f g) (chartNodes f g k hk)).comp
    DoubleSquareScalarPaths.coefficientPausedSquareParameter

/-- The common carrier recovers the whole original paused chart under the polynomial premap. -/
theorem chartFace_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (source f g)
      (chartFace f g k hk) n ((r, s), x) =
      ((InputCompositionTransformations.movingSquare k f g).pauseRight).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (projection.app Z)).map n x)) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex (source f g)
    (chartFace f g k hk) (chartNodes f g k hk) (r, s)
    (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, s)) rfl n x).trans ?_
  rw [CommonReferenceNerve.prespectrumFamily_eq, chart_family]
  exact (prespectrumSimplexFamily_precomp (InputCompositionChartNative.simplex k f g)
    (projectionMap (Z := Z)) n
    (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, s)) x).trans
      (InputCompositionChartNative.pausedSquare_native k f g n r s _)

/-- Every actual positive chart face value has the same full direct-input source reference. -/
theorem plusFace_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (source f g)
      (chartFace f g plus plus_projection) n ((r, s), x) =
      (InputCompositionCharts.plusChart f g).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (projection.app Z)).map n x)) :=
  chartFace_native f g plus plus_projection n r s x

/-- The inverse chart keeps its distinct original face in that identical reference carrier. -/
theorem minusFace_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (source f g)
      (chartFace f g minus minus_projection) n ((r, s), x) =
      (InputCompositionCharts.minusChart f g).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (projection.app Z)).map n x)) :=
  chartFace_native f g minus minus_projection n r s x

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionCarrierCharts
