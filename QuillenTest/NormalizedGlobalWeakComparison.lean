/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.OpenGluing.GlobalWeakComparison

/-!
# Canonical weak normalized comparisons

Behavioral consumers retain the actual overlap chart, original endpoint and
entire constant path, arbitrary base changes, zero-dimensional finite HELP,
empty overlap and base-change source, and genuine realization graph input.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen
open scoped Topology unitInterval Simplicial
universe u
variable {T : TopCat.{u}} {U V : Set T} (d : NormalizedFibrationSpan.Data T U V)
  (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
  (hp0 : HomotopyLiftingProperty d.p0.hom) (hp1 : HomotopyLiftingProperty d.p1.hom)
  (hR : HomotopyLiftingProperty (d.k0 ≫ d.q0).hom)
  (hgraph : ∀ (D : Type u) [TopologicalSpace D] [CompactSpace D] [LocallyCompactSpace D]
    (b : C(D,(U ∩ V : Set T))), IsClosed (Set.ofPred (fun z : D × (U ∩ V : Set T) ↦ b z.1 = z.2)))
  (hf0 : ∀ t : (U ∩ V : Set T), IsWeakHomotopyEquivalence
    (HomotopyFiber.strictMapOver (d.k0 ≫ d.q0).hom d.q0.hom d.k0.hom rfl t))
  (hf1 : ∀ t : (U ∩ V : Set T), IsWeakHomotopyEquivalence
    (HomotopyFiber.strictMapOver (d.k1 ≫ d.q1).hom d.q1.hom d.k1.hom rfl t))

example (m : d.Bridge) : (d.normalized.overlapChart hU hV m).val =
    d.normalized.totalFirst (d.normalized.firstBridge m) := rfl
example : (CubicalSubdivision.restriction d.normalized.projection.hom (U ∩ V)).comp
    (d.normalized.overlapChart hU hV).toHomotopyEquiv.toFun =
      d.bridgeProjection.hom := d.normalized.overlapChart_projection hU hV
example : UniversalStrictPullbackComparison d.normalized.projection.hom :=
  d.universalStrictPullbackComparison_of_weak_fibers hU hV hcover hp0 hp1 hR hgraph hf0 hf1
example {S : Type u} [TopologicalSpace S] (a : C(S,T)) :
    IsWeakHomotopyEquivalence (HomotopyPullback.strictPullbackInclusion d.normalized.projection.hom
      a) :=
  d.strictPullbackInclusion_isWeakHomotopyEquivalence_of_weak_fibers hU hV hcover hp0 hp1 hR hgraph
    hf0 hf1 a
example : IsWeakHomotopyEquivalence d.normalized.leftComparison :=
  d.leftComparison_isWeakHomotopyEquivalence_of_weak_fibers hU hV hcover hp0 hp1 hR hgraph hf0 hf1
example : IsWeakHomotopyEquivalence d.normalized.rightComparison :=
  d.rightComparison_isWeakHomotopyEquivalence_of_weak_fibers hU hV hcover hp0 hp1 hR hgraph hf0 hf1
example (e : d.E0) : (d.normalized.leftComparison e).val.1 = d.p0 e := rfl
example (e : d.E0) : (d.normalized.leftComparison e).val.2.1 = d.normalized.totalLeft e := rfl
example (e : d.E0) (t : unitInterval) : (d.normalized.leftComparison e).val.2.2 t = (d.p0 e).val :=
  rfl
example (e : d.E1) : (d.normalized.rightComparison e).val.1 = d.p1 e := rfl
example (e : d.E1) : (d.normalized.rightComparison e).val.2.1 = d.normalized.totalEnd e := rfl
example (e : d.E1) (t : unitInterval) : (d.normalized.rightComparison e).val.2.2 t = (d.p1 e).val :=
  rfl
example (X : SSet.{u}) (e : T ≃ₜ |X|) : UniversalStrictPullbackComparison
  d.normalized.projection.hom :=
  d.universalStrictPullbackComparison_of_weak_fibers_realizationModel hU hV hcover hp0 hp1 hR X e
    hf0 hf1
example (X : SSet.{u}) (e : T ≃ₜ |X|) (D : Type u) [TopologicalSpace D]
    [CompactSpace D] [LocallyCompactSpace D] (b : C(D,(U ∩ V : Set T))) :
    IsClosed (Set.ofPred (fun z : D × (U ∩ V : Set T) ↦ b z.1 = z.2)) :=
  NormalizedOpenGluing.Data.overlap_closedGraphs_of_realizationModel X e D b
example {S : Type u} [TopologicalSpace S] [IsEmpty S] (a : C(S,T)) :
    IsWeakHomotopyEquivalence (HomotopyPullback.strictPullbackInclusion d.normalized.projection.hom
      a) :=
  d.strictPullbackInclusion_isWeakHomotopyEquivalence_of_weak_fibers hU hV hcover hp0 hp1 hR hgraph
    hf0 hf1 a
example [IsEmpty (U ∩ V : Set T)] : UniversalStrictPullbackComparison d.normalized.projection.hom :=
  d.universalStrictPullbackComparison_of_weak_fibers hU hV hcover hp0 hp1 hR hgraph
    (fun t ↦ isEmptyElim t) (fun t ↦ isEmptyElim t)
example {S : Type u} [TopologicalSpace S] (a : C(S,T)) :
    FiniteCubeStrictHELP (HomotopyPullback.strictPullbackInclusion d.normalized.projection.hom a) :=
  (d.strictPullbackInclusion_isWeakHomotopyEquivalence_of_weak_fibers hU hV hcover hp0 hp1 hR hgraph
    hf0 hf1 a).cube_strictHELP
example {S : Type u} [TopologicalSpace S] (a : C(S,T))
    (x : C(CubicalTests.boundary.{u} 0,{z : S × d.normalized.Total // d.normalized.projection z.2 =
      a z.1}))
    (y : C(CubicalTests.cube.{u} 0,HomotopyPullback d.normalized.projection.hom a))
    (w : (HomotopyPullback.strictPullbackInclusion d.normalized.projection.hom a).comp x =
      y.comp (CubicalTests.boundaryInclusion 0).hom) :
    ∃ c : C(CubicalTests.cube.{u} 0,{z : S × d.normalized.Total // d.normalized.projection z.2 = a
      z.1}),
      c.comp (CubicalTests.boundaryInclusion 0).hom = x ∧
      Nonempty (((HomotopyPullback.strictPullbackInclusion d.normalized.projection.hom a).comp
        c).HomotopyRel y
        (Set.range (CubicalTests.boundaryInclusion 0))) :=
  (d.strictPullbackInclusion_isWeakHomotopyEquivalence_of_weak_fibers hU hV hcover hp0 hp1 hR hgraph
    hf0 hf1 a).cube_strictHELP 0 x y w
