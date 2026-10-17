/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetSourceBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeOverlap

/-!
# The original beta map on the complete source overlap

The source boundary is the actual realized beta map followed by its full anchored Laurent
coefficient node map. The same equality holds on each of the four original oriented realized
edges, with their unchanged quarter clocks. These are overlap identities in the full reference
nerve; the two polynomial chart endpoints are separate obligations.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u

namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
open BassH0Merge CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "J" => normalizedMap (polynomialProjection P a)

/-- The whole initial H0 row is the actual beta image with its complete source-boundary anchor. -/
theorem overlap_source_beta (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (t : I) :
    overlap P f E (y, (0, t)) =
      mapParameter (sourceBoundaryNode P f E)
        (SSet.toTop.map (beta P a E) (FourEdgeTree.overlap E J (y, t))) :=
  (overlap_source P f E y t).trans
    (congrArg (mapParameter (sourceBoundaryNode P f E)) (beta_overlap P a E y t).symm)

/-- The descended target tree has the prescribed beta value on the entire source overlap. -/
theorem tree_source_overlap_beta
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (t : I) :
    tree P f E (FourEdgeTree.overlap E J (y, t), 0) =
      mapParameter (sourceBoundaryNode P f E)
        (SSet.toTop.map (beta P a E) (FourEdgeTree.overlap E J (y, t))) :=
  (tree_overlap P f E y 0 t).trans (overlap_source_beta P f E y t)

/-- The positive normalization edge keeps its original reversed quarter clock. -/
theorem tree_source_edge12_beta
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (t : I) :
    tree P f E (FourEdgeTree.realizedEdge (FourEdgeTree.edge12 E J) (y, t), 0) =
      mapParameter (sourceBoundaryNode P f E)
        (SSet.toTop.map (beta P a E)
          (FourEdgeTree.realizedEdge (FourEdgeTree.edge12 E J) (y, t))) := by
  have h := tree_source_overlap_beta P f E y (FourEdgeTree.time12 t)
  have hq : FourEdgeTree.overlap E J (y, FourEdgeTree.time12 t) =
      FourEdgeTree.realizedEdge (FourEdgeTree.edge12 E J) (y, t) :=
    FourEdgeTree.overlap_quarter12 E J y t
  rw [hq] at h
  exact h

/-- The positive geometric edge keeps its separate original reversed quarter clock. -/
theorem tree_source_edge01_beta
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (t : I) :
    tree P f E (FourEdgeTree.realizedEdge (FourEdgeTree.edge01 E J) (y, t), 0) =
      mapParameter (sourceBoundaryNode P f E)
        (SSet.toTop.map (beta P a E)
          (FourEdgeTree.realizedEdge (FourEdgeTree.edge01 E J) (y, t))) := by
  have h := tree_source_overlap_beta P f E y (FourEdgeTree.time01 t)
  have hq : FourEdgeTree.overlap E J (y, FourEdgeTree.time01 t) =
      FourEdgeTree.realizedEdge (FourEdgeTree.edge01 E J) (y, t) :=
    FourEdgeTree.overlap_quarter01 E J y t
  rw [hq] at h
  exact h

/-- The inverse geometric edge keeps its original forward quarter clock. -/
theorem tree_source_edge03_beta
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (t : I) :
    tree P f E (FourEdgeTree.realizedEdge (FourEdgeTree.edge03 E J) (y, t), 0) =
      mapParameter (sourceBoundaryNode P f E)
        (SSet.toTop.map (beta P a E)
          (FourEdgeTree.realizedEdge (FourEdgeTree.edge03 E J) (y, t))) := by
  have h := tree_source_overlap_beta P f E y (FourEdgeTree.time03 t)
  have hq : FourEdgeTree.overlap E J (y, FourEdgeTree.time03 t) =
      FourEdgeTree.realizedEdge (FourEdgeTree.edge03 E J) (y, t) :=
    FourEdgeTree.overlap_quarter03 E J y t
  rw [hq] at h
  exact h

/-- The inverse normalization edge keeps its distinct final quarter clock. -/
theorem tree_source_edge34_beta
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (t : I) :
    tree P f E (FourEdgeTree.realizedEdge (FourEdgeTree.edge34 E J) (y, t), 0) =
      mapParameter (sourceBoundaryNode P f E)
        (SSet.toTop.map (beta P a E)
          (FourEdgeTree.realizedEdge (FourEdgeTree.edge34 E J) (y, t))) := by
  have h := tree_source_overlap_beta P f E y (FourEdgeTree.time34 t)
  have hq : FourEdgeTree.overlap E J (y, FourEdgeTree.time34 t) =
      FourEdgeTree.realizedEdge (FourEdgeTree.edge34 E J) (y, t) :=
    FourEdgeTree.overlap_quarter34 E J y t
  rw [hq] at h
  exact h

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
