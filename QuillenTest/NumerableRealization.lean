/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.Realization.MetricRealizationDomination

/-! Named regressions for the actual classifier, both maps and composite homotopy. -/
@[expose] public section
noncomputable section
open Convexity CategoryTheory Opposite
open scoped Topology Simplicial
universe u v w
namespace QuillenTest.NumerableRealization

open Quillen
open NumerableConnectorCover
variable {A : Type u} [TopologicalSpace A] {ι : Type v} [LinearOrder ι]

/-- Finite-support enlargement only inserts zero coefficients. -/
theorem original_coefficients (ρ : PartitionOfUnity ι A) {s t : Finset ι}
    (hst : s ⊆ t) (x : chartDomain ρ s) :
    (finiteChart ρ s x).map (finiteFaceInclusion hst) =
      finiteChart ρ t ⟨x.1, x.2.trans hst⟩ := finiteChart_map_inclusion ρ hst x

omit [TopologicalSpace A] in
/-- Finite inclusions identify the original weak-realization charts exactly. -/
theorem original_chart_inclusion (W : ι → Set A) {s t : Finset ι}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t)
    (hsface : IsNerveFace W s) (htface : IsNerveFace W t) (x : StdSimplex ℝ s) :
    finiteNerveChart W t ht htface (x.map (finiteFaceInclusion hst)) =
      finiteNerveChart W s hs hsface x := finiteNerveChart_inclusion W hs ht hst hsface htface x

/-- The actual classifier uses the given partition, not a replacement system of coefficients. -/
theorem classifier_uses_partition (W : ι → Set A) (ρ : PartitionOfUnity ι A)
    (hρ : ρ.IsSubordinate W) (x : A) :
    partitionNerveMap W ρ hρ x =
      finiteNerveChart W (ρ.finsupport x) (partition_finsupport_nonempty ρ x)
        (partition_support_isNerveFace W ρ hρ x)
        (finiteChart ρ (ρ.finsupport x) ⟨x, Finset.Subset.refl _⟩) := rfl

/-- Any controlling finite face gives the same classifier value, including zero coordinates. -/
theorem finite_local_factorization (W : ι → Set A) (ρ : PartitionOfUnity ι A)
    (hρ : ρ.IsSubordinate W) (s : Finset ι) (hs : s.Nonempty)
    (hface : IsNerveFace W s) (x : chartDomain ρ s) :
    partitionNerveValue W ρ hρ x.1 = finiteNerveChart W s hs hface (finiteChart ρ s x) :=
  partitionNerveValue_eq_chart W ρ hρ s hs hface x

/-- Continuity is for the genuine weak realization, not just its individual coordinate functions. -/
theorem actual_classifier_continuity (W : ι → Set A) (ρ : PartitionOfUnity ι A)
    (hρ : ρ.IsSubordinate W) : Continuous (partitionNerveMap W ρ hρ) :=
  (partitionNerveMap W ρ hρ).continuous

/-- The constructed homotopy has the literal composite and identity as endpoints. -/
theorem actual_composite_endpoints {κ : Type w} (E : LocalEquiconnection A)
    (W : ι → Set A) (V : κ → Set A) (hconvex : ∀ k, E.IsConvex (V k))
    (href : PointStarRefines W V) (hcover : ∀ x, ∃ i, x ∈ W i)
    (vertex : ι → A) (hvertex : ∀ i, vertex i ∈ W i)
    (ρ : PartitionOfUnity ι A) (hρ : ρ.IsSubordinate W) (x : A) :
    numerableDominationHomotopy E W V hconvex href hcover vertex hvertex ρ hρ (0, x) =
      nerveReturnMap E W V hconvex href vertex hvertex (partitionNerveMap W ρ hρ x) ∧
    numerableDominationHomotopy E W V hconvex href hcover vertex hvertex ρ hρ (1, x) = x :=
  ⟨ContinuousMap.Homotopy.map_zero_left _ x, ContinuousMap.Homotopy.map_one_left _ x⟩

/-- The metric theorem constructs every radius, cover refinement and partition internally. -/
theorem metric_geometric_inputs_only {B : Type u} [MetricSpace B] {κ : Type w}
    (E : LocalEquiconnection B) (V : κ → Set B) (hopen : ∀ k, IsOpen (V k))
    (hconvex : ∀ k, E.IsConvex (V k)) (hcover : ∀ x, ∃ k, x ∈ V k) :
    ∃ (K : SSet.{u}) (a : C(B, |K|)) (b : C(|K|, B)),
      Nonempty ((b.comp a).Homotopy (ContinuousMap.id B)) :=
  exists_metric_realization_domination E V hopen hconvex hcover

end QuillenTest.NumerableRealization
