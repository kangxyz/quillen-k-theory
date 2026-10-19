/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedEvaluationCarrier
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedCarrier
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputRawChartProductNodes
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFiniteParameter
public import Quillen.Waldhausen.SConstruction.Iterated.RealizationSimplexComposition

/-!
# The original raw chart square on every evaluation-carrier polynomial point

The finite five-node geometric square is composed with the whole polynomial reference nerve.
The actual finite-factor realization comparison gives a continuous parameter, with both full
endpoint node maps and the entire original reverse-forward clock. Native evaluation is proved
pointwise from the actual product family; no whole-nerve native continuity is assumed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedPostProduct
open GlobalSectionChangeIndex CommonReferenceNerve

private theorem product_family {V W T : Model.{u}} {p q : ℕ}
    (F : V ⟶ T) (H : V ⟶ W) (G : W ⟶ T)
    (a : F.functor ≅ (H ≫ G).functor)
    (N : Fin (p + 1) → Node H) (M : Fin (q + 1) → Node G) (n : ℕ) :
    prespectrumFamily F
      (FiniteParameter.gridNodes H F (fun A i => CommonReferenceProduct.node F H G a A (M i)) N)
      n =
    prespectrumSimplexFamily
      (CommonReferenceProduct.simplex H (fun i => (N i).1) (fun i => (N i).2)
        G (fun i => (M i).1) (fun i => (M i).2)) n := by
  rw [prespectrumFamily_eq]
  apply congrArg (fun S => prespectrumSimplexFamily S n)
  exact ModelSimplex.ofIsos_change_reference a
    (CommonReferenceProduct.vertices (fun i => (N i).1) (fun i => (M i).1))
    (CommonReferenceProduct.references H (fun i => (N i).1) (fun i => (N i).2)
      G (fun i => (M i).1) (fun i => (M i).2))

private theorem finite_product_native {V W T : Model.{u}} {q : ℕ}
    (F : V ⟶ T) (H : V ⟶ W) (G : W ⟶ T)
    (a : F.functor ≅ (H ≫ G).functor) (M : Fin (q + 1) → Node G)
    (n : ℕ) (y : |nerve (Codiscrete (Node H))|)
    (w : StdSimplex ℝ (Fin (q + 1))) (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily F n
      (FiniteParameter.parameter H F
        (fun A i => CommonReferenceProduct.node F H G a A (M i)) (y, w)) x =
    prespectrumFamily G M n (w, pointwisePrespectrumFamily H n y x) := by
  obtain ⟨p, N, z, rfl⟩ := exists_parameter H y
  rw [FiniteParameter.parameter_characteristic, pointwisePrespectrumFamily_parameter,
    pointwisePrespectrumFamily_parameter, product_family, prespectrumFamily_eq,
    prespectrumFamily_eq]
  exact CommonReferenceProduct.prespectrum_comp H (fun i => (N i).1) (fun i => (N i).2)
    G (fun i => (M i).1) (fun i => (M i).2) n x z w

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
local notation "F" => InputSeedEvaluationCarrier.polyRef Y
local notation "G" => InputSeedCarrier.laurentRef g
local notation "R" => InputRawChartRows.squareSource g plus

/-- Every complete polynomial node composes with each original raw square node. -/
def productNode (N : Node F) (i : Fin 5) : Node G :=
  CommonReferenceProduct.node G F R
    (InputRawChartProductNodes.anchor g plus GlobalRawBass.plus_projection) N
    (NativeSquareFiveSimplex.nodes (laurent.map g) (plus.app Y) (plus.app X)
      (polynomial.map g) (plus.naturality g) i)

/-- The actual whole-nerve parameter uses the original finite raw square and its original clock. -/
def parameter : C(|nerve (Codiscrete (Node F))| × I, |nerve (Codiscrete (Node G))|) :=
  (FiniteParameter.parameter F G (productNode g)).comp
    ⟨fun z => (z.1, NativeSquareFiveSimplex.parameter z.2), by fun_prop⟩

/-- The whole initial column is the induced map of complete original source nodes. -/
theorem parameter_zero (y : |nerve (Codiscrete (Node F))|) :
    parameter g (y, 0) = mapParameter (fun N => productNode g N 2) y := by
  change FiniteParameter.parameter F G (productNode g)
    (y, NativeSquareFiveSimplex.parameter 0) = _
  rw [Path.source]
  exact FiniteParameter.parameter_vertex F G (productNode g) 2 y

/-- The whole terminal column retains its distinct actual raw suffix nodes. -/
theorem parameter_one (y : |nerve (Codiscrete (Node F))|) :
    parameter g (y, 1) = mapParameter (fun N => productNode g N 4) y := by
  change FiniteParameter.parameter F G (productNode g)
    (y, NativeSquareFiveSimplex.parameter 1) = _
  rw [Path.target]
  exact FiniteParameter.parameter_vertex F G (productNode g) 4 y

/-- Every finite source family gives precisely the original complete product grid. -/
theorem parameter_characteristic {k : ℕ} (N : Fin (k + 1) → Node F)
    (z : StdSimplex ℝ (Fin (k + 1))) (s : I) :
    parameter g (CommonReferenceNerve.parameter F N z, s) =
      CommonReferenceNerve.parameter G (FiniteParameter.gridNodes F G (productNode g) N)
        (Quillen.SimplexGrid.parameter.{u+1} k 4 (z, NativeSquareFiveSimplex.parameter s)) :=
  FiniteParameter.parameter_characteristic F G (productNode g) N z
    (NativeSquareFiveSimplex.parameter s)

/-- The whole original geometric square acts on the unchanged native polynomial point. -/
theorem native (n : ℕ) (y : |nerve (Codiscrete (Node F))|) (s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    pointwisePrespectrumFamily G n (parameter g (y, s)) x =
      (boundedFlatPerfectPrespectrumSquareHomotopy (laurent.map g) (plus.app Y)
        (plus.app X) (polynomial.map g) (plus.naturality g)).level n
          (s, pointwisePrespectrumFamily F n y x) := by
  exact (finite_product_native G F R
    (InputRawChartProductNodes.anchor g plus GlobalRawBass.plus_projection)
    (NativeSquareFiveSimplex.nodes (laurent.map g) (plus.app Y) (plus.app X)
      (polynomial.map g) (plus.naturality g)) n y (NativeSquareFiveSimplex.parameter s) x).trans
    ((congrArg (fun f => f (NativeSquareFiveSimplex.parameter s,
      pointwisePrespectrumFamily F n y x))
      (prespectrumFamily_eq R
        (NativeSquareFiveSimplex.nodes (laurent.map g) (plus.app Y) (plus.app X)
          (polynomial.map g) (plus.naturality g)) n)).trans
      (NativeSquareFiveSimplex.native (laurent.map g) (plus.app Y) (plus.app X)
        (polynomial.map g) (plus.naturality g) n s (pointwisePrespectrumFamily F n y x)))

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedPostProduct
