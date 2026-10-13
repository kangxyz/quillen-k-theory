/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.HomotopyPullback.UniversalComparison
public import Quillen.Topology.OpenGluing.FirstUniversalComparison

/-!
# Regression consumers for exact universal comparison transport

These tests check arbitrary parameter spaces, exact source-comparison squares,
and the actual first normalized chart. Universal base-change weakness remains
an explicit input.
-/
@[expose] public section

noncomputable section
open Quillen Quillen.HomotopyPullback Quillen.PathSubdivision
open Quillen.FiberwiseMappingPath Quillen.CubicalSubdivision
open scoped Topology unitInterval
universe u

section Transport
variable {E F B D : Type u}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B] [TopologicalSpace D]
  (q : C(F,B)) (f : C(E,F))

example (g : C(D,B)) :
    (sourceMap g q f).comp (strictPullbackInclusion (q.comp f) g) =
      (strictPullbackInclusion q g).comp (baseChangedMap q f g) := rfl

example (hs : UniversalStrictPullbackComparison (q.comp f))
    (hb : ∀ (A : Type u) [TopologicalSpace A] (g : C(A,B)),
      IsWeakHomotopyEquivalence (baseChangedMap q f g)) :
    UniversalStrictPullbackComparison q :=
  UniversalStrictPullbackComparison.of_baseChanges q f hs hb
end Transport

section Normalized
open CategoryTheory
variable {T : TopCat.{u}} {U V : Set T} (d : NormalizedFibrationSpan.Data T U V)
  (hU : IsOpen U) (hV : IsOpen V)
  (hp0 : CompactHomotopyLiftingProperty d.p0.hom)
  (hbridge : ∀ (A : Type u) [TopologicalSpace A] (g : C(A,T)),
    IsWeakHomotopyEquivalence
      (baseChangedMap d.normalized.bridgeBase.hom d.normalized.i0.hom g))

example : UniversalStrictPullbackComparison d.normalized.firstProjection.hom :=
  d.firstProjection_universalStrictPullbackComparison_of_compact hV hp0 hbridge

example : UniversalStrictPullbackComparison
    (restriction d.normalized.projection.hom U) :=
  d.leftRestriction_universalStrictPullbackComparison_of_compact hU hV hp0 hbridge
end Normalized
