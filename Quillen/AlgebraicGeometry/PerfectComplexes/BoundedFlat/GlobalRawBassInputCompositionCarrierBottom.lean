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

/-!
# The original Laurent-composition bottom in the common input carrier

The actual five-node Bass projection path is composed with the original three-node Laurent
composition. Its complete fifteen-node product is transported to the unchanged direct input
reference using only the original map composition and projection equations. The two original
coordinates remain independent at every native level.
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
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionCarrierBottom
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The genuine source of the original split Laurent composition triangle. -/
abbrev laurentSource :=
  BinaryNormalizationSimplex.sourceMap (laurent.map f) (laurent.map g)

/-- The actual source, intermediate and target of Laurent composition, in their original order. -/
def laurentVertices : Fin 3 →
    (modelOf (boundedFlatPerfectWaldhausen (laurent.obj Z)) ⟶
      modelOf (boundedFlatPerfectWaldhausen (laurent.obj X))) :=
  ![laurentSource f g,
    BinaryNormalizationSimplex.intermediateMap (laurent.map f) (laurent.map g),
    BinaryNormalizationSimplex.targetMap (laurent.map f) (laurent.map g)]

/-- The original split transformations give all complete Laurent triangle references. -/
def laurentReferences : ∀ i, (laurentSource f g).functor ≅ (laurentVertices f g i).functor :=
  Fin.cases (Iso.refl _)
    (Fin.cases (BinaryNormalizationSimplex.first (laurent.map f) (laurent.map g))
      (Fin.cases (BinaryNormalizationSimplex.total (laurent.map f) (laurent.map g))
        (fun i ↦ Fin.elim0 i)))

/-- The actual reference of the independent projection/composition product. -/
abbrev productSource := InputIdentityProjection.source Z ≫ laurentSource f g

/-- The actual functor composition and original positive projection identify the total map. -/
theorem total :
    (laurent.map f ≫ laurent.map g) ≫ (plus.app Z ≫ projection.app Z) =
      laurent.map (f ≫ g) ≫ laurentProjection.app Z := by
  rw [plus_projection Z, ← laurent.map_comp f g]

/-- Only the genuine total equality and original composition iso change the common reference. -/
def sourceIso : (InputCompositionCarrierCharts.source f g).functor ≅
    (productSource f g).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedFlatNormalizedPullback (total f g).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (laurent.map f ≫ laurent.map g)
        (plus.app Z ≫ projection.app Z)) AsSmall.up)

/-- All fifteen actual product vertices keep their complete reference isomorphisms. -/
def productNodes (i : Fin 15) : CommonReferenceNerve.Node (productSource f g) :=
  ⟨CommonReferenceProduct.vertices (fun j ↦ (InputIdentityProjection.nodes Z j).1)
      (laurentVertices f g) i,
    CommonReferenceProduct.references (InputIdentityProjection.source Z)
      (fun j ↦ (InputIdentityProjection.nodes Z j).1)
      (fun j ↦ (InputIdentityProjection.nodes Z j).2)
      (laurentSource f g) (laurentVertices f g) (laurentReferences f g) i⟩

/-- The entire product lies in the same full-reference carrier as the direct and chart faces. -/
def nodes : Fin 15 → InputCompositionCarrierCharts.Node f g :=
  ModelSimplex.reanchorNodes (sourceIso f g) (productNodes f g)

/-- Reanchoring retains the entire original product model simplex. -/
theorem product_family :
    ModelSimplex.ofIsos (InputCompositionCarrierCharts.source f g)
      (fun i ↦ (nodes f g i).1) (fun i ↦ (nodes f g i).2) =
        CommonReferenceProduct.simplex (InputIdentityProjection.source Z)
          (fun j ↦ (InputIdentityProjection.nodes Z j).1)
          (fun j ↦ (InputIdentityProjection.nodes Z j).2)
          (laurentSource f g) (laurentVertices f g) (laurentReferences f g) :=
  ModelSimplex.ofIsos_change_reference (sourceIso f g)
    (fun i ↦ (productNodes f g i).1) (fun i ↦ (productNodes f g i).2)

/-- The actual Bass height and split Laurent time are the original independent product clocks. -/
def parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 15)) :=
  ⟨fun z ↦ Quillen.SimplexGrid.parameter.{u + 1} 4 2
    (InputIdentityProjection.parameter z.2, binaryPath (k := 2) 0 1 2 z.1), by fun_prop⟩

/-- The complete original Laurent-composition bottom face in the common reference carrier. -/
def face : C(unitInterval × unitInterval, InputCompositionCarrierCharts.Carrier f g) :=
  (CommonReferenceNerve.parameter (InputCompositionCarrierCharts.source f g) (nodes f g)).comp
    parameter.{u}

/-- Every original bottom value retains both actual clocks, all levels and all input points. -/
theorem face_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (face f g) n ((r, t), x) =
      (InputCompositionCharts.laurentTrack f g).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (t, x)) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
    (InputCompositionCarrierCharts.source f g) (face f g) (nodes f g) (r, t)
    (parameter.{u} (r, t)) rfl n x).trans ?_
  rw [CommonReferenceNerve.prespectrumFamily_eq, product_family]
  refine (CommonReferenceProduct.prespectrum_comp (InputIdentityProjection.source Z)
    (fun j ↦ (InputIdentityProjection.nodes Z j).1)
    (fun j ↦ (InputIdentityProjection.nodes Z j).2)
    (laurentSource f g) (laurentVertices f g) (laurentReferences f g)
    n x (InputIdentityProjection.parameter t) (binaryPath (k := 2) 0 1 2 r)).trans ?_
  refine (BinaryNormalizationSimplex.native_path (laurent.map f) (laurent.map g)
    n r _).trans ?_
  exact congrArg (fun y ↦ (InputCompositionCharts.laurentComposition f g).level n (r, y))
    (InputIdentityProjection.native Z n t x)

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionCarrierBottom
