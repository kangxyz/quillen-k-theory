/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionTerminalAttach
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeSquareFiveSimplex
public import Quillen.Waldhausen.SConstruction.Iterated.RealizationSimplexComposition

/-!
# Actual two-square product pieces of the terminal input face

The original polynomial square for the second arrow is followed by the original positive or
inverse square for the first arrow. The complete twenty-five-node products use their original
five-node paths and independent clocks, with an actual total-map anchor to the direct source.
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
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTerminalProducts
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The literal source of the original second-arrow polynomial square. -/
abbrev polynomialSource := NativeSquareFiveSimplex.source (polynomial.map g) (projection.app Z)

/-- All five original polynomial nodes, with the actual projection naturality transport. -/
abbrev polynomialNodes := NativeSquareFiveSimplex.nodes (polynomial.map g) (projection.app Z)
  (projection.app Y) g (projection.naturality g)

variable (k : laurent ⟶ polynomial)
  (hk : ∀ V, k.app V ≫ projection.app V = laurentProjection.app V)

/-- The original chart-square reference uses the first scheme arrow, without a composite cast. -/
abbrev chartSource := NativeSquareFiveSimplex.source (laurent.map f) (k.app Y)

/-- The five complete chart nodes retain the actual positive or inverse naturality equality. -/
abbrev chartNodes := NativeSquareFiveSimplex.nodes (laurent.map f) (k.app Y)
  (k.app X) (polynomial.map f) (k.naturality f)

/-- The original independent two-square source before the common-reference anchor. -/
abbrev productSource := polynomialSource g ≫ chartSource f k

include hk in
/-- Actual chart naturality, projection and functor composition identify the product total. -/
theorem total :
    (laurent.map f ≫ k.app Y) ≫ (polynomial.map g ≫ projection.app Z) =
      laurent.map (f ≫ g) ≫ laurentProjection.app Z := by
  rw [Category.assoc, ← Category.assoc (k.app Y), ← k.naturality g]
  rw [Category.assoc (laurent.map g), hk Z, ← Category.assoc, ← laurent.map_comp f g]

/-- The actual geometric composition iso anchors both square factors at the unchanged source. -/
def sourceIso : (InputCompositionCarrierCharts.source f g).functor ≅
    (productSource f g k).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedFlatNormalizedPullback (total f g k hk).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (laurent.map f ≫ k.app Y)
        (polynomial.map g ≫ projection.app Z)) AsSmall.up)

/-- All twenty-five product vertices retain their full original composition references. -/
def productNodes (i : Fin 25) : CommonReferenceNerve.Node (productSource f g k) :=
  ⟨CommonReferenceProduct.vertices (fun j ↦ (polynomialNodes g j).1)
      (fun j ↦ (chartNodes f k j).1) i,
    CommonReferenceProduct.references (polynomialSource g)
      (fun j ↦ (polynomialNodes g j).1) (fun j ↦ (polynomialNodes g j).2)
      (chartSource f k) (fun j ↦ (chartNodes f k j).1) (fun j ↦ (chartNodes f k j).2) i⟩

/-- The whole product has the same complete reference source as all original composition faces. -/
def nodes : Fin 25 → InputCompositionCarrierCharts.Node f g :=
  ModelSimplex.reanchorNodes (sourceIso f g k hk) (productNodes f g k)

/-- Actual reanchoring leaves the entire two-square model simplex unchanged. -/
theorem product_family :
    ModelSimplex.ofIsos (InputCompositionCarrierCharts.source f g)
      (fun i ↦ (nodes f g k hk i).1) (fun i ↦ (nodes f g k hk i).2) =
        CommonReferenceProduct.simplex (polynomialSource g)
          (fun j ↦ (polynomialNodes g j).1) (fun j ↦ (polynomialNodes g j).2)
          (chartSource f k) (fun j ↦ (chartNodes f k j).1) (fun j ↦ (chartNodes f k j).2) :=
  ModelSimplex.ofIsos_change_reference (sourceIso f g k hk)
    (fun i ↦ (productNodes f g k i).1) (fun i ↦ (productNodes f g k i).2)

/-- Both original five-node paths keep their independent comparison and overlap parameters. -/
def parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 25)) :=
  ⟨fun z ↦ Quillen.SimplexGrid.parameter.{u + 1} 4 4
    (NativeSquareFiveSimplex.parameter z.2, NativeSquareFiveSimplex.parameter z.1), by fun_prop⟩

/-- The entire actual positive or inverse square-product piece in the common carrier. -/
def face : C(unitInterval × unitInterval, InputCompositionCarrierCharts.Carrier f g) :=
  (CommonReferenceNerve.parameter (InputCompositionCarrierCharts.source f g) (nodes f g k hk)).comp
    parameter.{u}

/-- The whole product is exactly the original native chart square applied to polynomial square. -/
theorem face_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (face f g k hk) n ((s, t), x) =
      (boundedFlatPerfectPrespectrumSquareHomotopy (laurent.map f) (k.app Y)
        (k.app X) (polynomial.map f) (k.naturality f)).level n
          (s, (polynomialSquareHomotopy g).level n (t, x)) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
    (InputCompositionCarrierCharts.source f g) (face f g k hk) (nodes f g k hk) (s, t)
    (parameter.{u} (s, t)) rfl n x).trans ?_
  rw [CommonReferenceNerve.prespectrumFamily_eq, product_family]
  refine (CommonReferenceProduct.prespectrum_comp (polynomialSource g)
    (fun j ↦ (polynomialNodes g j).1) (fun j ↦ (polynomialNodes g j).2)
    (chartSource f k) (fun j ↦ (chartNodes f k j).1) (fun j ↦ (chartNodes f k j).2)
    n x (NativeSquareFiveSimplex.parameter t) (NativeSquareFiveSimplex.parameter s)).trans ?_
  refine (NativeSquareFiveSimplex.native (laurent.map f) (k.app Y) (k.app X)
    (polynomial.map f) (k.naturality f) n s _).trans ?_
  exact congrArg (fun y ↦ (boundedFlatPerfectPrespectrumSquareHomotopy
    (laurent.map f) (k.app Y) (k.app X) (polynomial.map f) (k.naturality f)).level n (s, y))
      (NativeSquareFiveSimplex.native (polynomial.map g) (projection.app Z)
        (projection.app Y) g (projection.naturality g) n t x)

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTerminalProducts
