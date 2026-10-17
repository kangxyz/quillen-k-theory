/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFiniteParameter
public import Quillen.Waldhausen.SConstruction.Iterated.RealizationSimplexComposition
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceProductNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MInternalBoundaryRows

/-!
# The original two-chart overlap path over a whole coefficient reference

The finite second factor is the unchanged five-node Bass projection path. Its reversed
positive half and negative half keep their four original quarter intervals. Both complete
chart endpoints and every compact native evaluation are retained, including level zero.
No global prespectrum evaluator on an unrestricted nerve product is used.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference
open BassReferenceMerge CommonReferenceNerve
attribute [local irreducible] boundedFlatNormalizedPullback

private theorem pair_reference_other {V W T : Model.{u}}
    {E E' : V ⟶ W} {G G' : W ⟶ T} (e : E.functor ≅ E'.functor)
    (g : G.functor ≅ G'.functor) :
    (Functor.uncurry.obj (whiskeringLeft V W T)).mapIso (e.prod g) =
      isoWhiskerLeft E.functor g ≪≫ isoWhiskerRight e G'.functor := by
  apply Iso.ext
  ext X
  exact g.hom.naturality (e.hom.app X)

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))

/-- The target reference is the literal composite with the original projection-path source. -/
abbrev reference := E ≫ BassProjectionPath.source P a

/-- Compose both complete references; the five old projection nodes remain unchanged. -/
def nodes (e : CommonReferenceNerve.Node E) (j : Fin 5) :
    CommonReferenceNerve.Node (reference P a E) :=
  ⟨e.1 ≫ (BassProjectionPath.nodes P a j).1,
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      (e.2.prod (BassProjectionPath.nodes P a j).2)⟩

/-- The whole coefficient nerve carries the exact old four-edge overlap parameter. -/
def family : C(|nerve (Codiscrete (CommonReferenceNerve.Node E))| × unitInterval,
    |nerve (Codiscrete (CommonReferenceNerve.Node (reference P a E)))|) :=
  (FiniteParameter.parameter E (reference P a E) (nodes P a E)).comp
    ⟨fun z ↦ (z.1, BassProjectionPath.parameter z.2), by fun_prop⟩

/-- Restricting any coefficient chain gives exactly its original finite product grid. -/
theorem family_characteristic {p : ℕ} (N : Fin (p + 1) → CommonReferenceNerve.Node E)
    (z : StdSimplex ℝ (Fin (p + 1))) (t : unitInterval) :
    family P a E (CommonReferenceNerve.parameter E N z, t) =
      CommonReferenceNerve.parameter (reference P a E)
        (FiniteParameter.gridNodes E (reference P a E) (nodes P a E) N)
        (SimplexGrid.parameter.{u + 1} p 4 (z, BassProjectionPath.parameter t)) :=
  FiniteParameter.parameter_characteristic E (reference P a E) (nodes P a E)
    N z (BassProjectionPath.parameter t)

/-- The actual chart endpoint keeps its polynomial projection, chart map and normalization. -/
def chartNode (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
    (e : CommonReferenceNerve.Node E) : CommonReferenceNerve.Node (reference P a E) :=
  CommonReferenceProduct.postNode (reference P a E) (BassMJoin.endpointMap (c := a) P α)
    (isoWhiskerLeft E.functor (BassMJoin.projectionEndpointIso (c := a) P α ha)) e

/-- An original projection endpoint identifies its full induced chart attachment. -/
theorem nodes_endpoint
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
    (j : Fin 5)
    (hj : BassProjectionPath.nodes P a j =
      ⟨BassMJoin.endpointMap (c := a) P α, BassMJoin.projectionEndpointIso (c := a) P α ha⟩)
    (e : CommonReferenceNerve.Node E) : nodes P a E e j = chartNode P a E α ha e := by
  let composeNode : BassProjectionPath.Node P a →
      CommonReferenceNerve.Node (reference P a E) := fun m ↦
    ⟨e.1 ≫ m.1,
      (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso (e.2.prod m.2)⟩
  calc
    _ = composeNode (BassProjectionPath.nodes P a j) := rfl
    _ = composeNode
        ⟨BassMJoin.endpointMap (c := a) P α,
          BassMJoin.projectionEndpointIso (c := a) P α ha⟩ := congrArg composeNode hj
    _ = _ := by
      simp only [composeNode, chartNode, CommonReferenceProduct.postNode,
        CommonReferenceProduct.reanchor, CommonReferenceNerve.postcompNode, pair_reference_other]

/-- The whole initial endpoint is the positive chart map on every complete coefficient node. -/
theorem family_zero (x : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) :
    family P a E (x, 0) =
      mapParameter (chartNode P a E (underToLaurent R) (laurentPlus_projection P a)) x := by
  change FiniteParameter.parameter E (reference P a E) (nodes P a E)
    (x, BassProjectionPath.parameter 0) = _
  rw [Path.source, FiniteParameter.parameter_vertex]
  apply congrArg (fun f ↦ mapParameter f x)
  funext e
  exact nodes_endpoint P a E (underToLaurent R) (laurentPlus_projection P a) 2
    (BassMJoin.plus_endpoint_node P) e

/-- The whole terminal endpoint retains the inverse chart's separate source equality cast. -/
theorem family_one (x : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) :
    family P a E (x, 1) =
      mapParameter (chartNode P a E (underToLaurentInvert R) (laurentMinus_projection P a)) x := by
  change FiniteParameter.parameter E (reference P a E) (nodes P a E)
    (x, BassProjectionPath.parameter 1) = _
  rw [Path.target, FiniteParameter.parameter_vertex]
  apply congrArg (fun f ↦ mapParameter f x)
  funext e
  exact nodes_endpoint P a E (underToLaurentInvert R) (laurentMinus_projection P a) 4
    (BassMJoin.minus_endpoint_node P) e

/-- Every finite coefficient family has the old overlap value at every original level. -/
theorem finite_native {p : ℕ} (N : Fin (p + 1) → CommonReferenceNerve.Node E)
    (n : ℕ) (z : StdSimplex ℝ (Fin (p + 1))) (t : unitInterval)
    (x : (prespectrum V).space n) :
    prespectrumFamily (reference P a E)
      (FiniteParameter.gridNodes E (reference P a E) (nodes P a E) N) n
      (SimplexGrid.parameter.{u + 1} p 4 (z, BassProjectionPath.parameter t), x) =
      (boundedFlatCoefficientBassSquareHomotopy P a).level n
        (t, prespectrumFamily E N n (z, x)) := by
  rw [prespectrumFamily_eq, prespectrumFamily_eq]
  change prespectrumSimplexFamily
    (CommonReferenceProduct.simplex E (fun i ↦ (N i).1) (fun i ↦ (N i).2)
      (BassProjectionPath.source P a) (fun j ↦ (BassProjectionPath.nodes P a j).1)
      (fun j ↦ (BassProjectionPath.nodes P a j).2)) n
    (SimplexGrid.parameter.{u + 1} p 4 (z, BassProjectionPath.parameter t), x) = _
  rw [CommonReferenceProduct.prespectrum_comp]
  exact BassProjectionPath.native P a n t _

variable {T : Type v} [TopologicalSpace T] [CompactSpace T]

/-- A compact coefficient parameter retains an independent original overlap coordinate. -/
def compactParameter (p : C(T, |nerve (Codiscrete (CommonReferenceNerve.Node E))|)) :
    C(T × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node (reference P a E)))|) :=
  (family P a E).comp ⟨fun z ↦ (p z.1, z.2), by fun_prop⟩

/-- Exact compact evaluation of the whole-nerve family, without global evaluator continuity. -/
theorem compact_native (p : C(T, |nerve (Codiscrete (CommonReferenceNerve.Node E))|))
    (n : ℕ) (s : T) (t : unitInterval) (x : (prespectrum V).space n) :
    compactPrespectrumFamily (reference P a E) (compactParameter P a E p) n ((s, t), x) =
      (boundedFlatCoefficientBassSquareHomotopy P a).level n
        (t, compactPrespectrumFamily E p n (s, x)) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter E (p s)
  have hp : compactParameter P a E p (s, t) =
      CommonReferenceNerve.parameter (reference P a E)
        (FiniteParameter.gridNodes E (reference P a E) (nodes P a E) N)
        (SimplexGrid.parameter.{u + 1} k 4 (z, BassProjectionPath.parameter t)) := by
    change family P a E (p s, t) = _
    rw [← hz]
    exact family_characteristic P a E N z t
  calc
    _ = prespectrumFamily (reference P a E)
        (FiniteParameter.gridNodes E (reference P a E) (nodes P a E) N) n
        (SimplexGrid.parameter.{u + 1} k 4 (z, BassProjectionPath.parameter t), x) :=
      compactPrespectrumFamily_eq_simplex (reference P a E) (compactParameter P a E p)
        _ (s, t) _ hp n x
    _ = (boundedFlatCoefficientBassSquareHomotopy P a).level n
        (t, prespectrumFamily E N n (z, x)) := finite_native P a E N n z t x
    _ = _ := congrArg (fun y ↦ (boundedFlatCoefficientBassSquareHomotopy P a).level n (t, y))
      (compactPrespectrumFamily_eq_simplex E p N s z hz.symm n x).symm

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference
