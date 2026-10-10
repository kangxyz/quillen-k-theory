/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Topology.Realization.FiniteNullhomotopy

/-!
# Finite-support weak-contractibility consumers

Tests retain the literal whole boundary, actual homotopy-group map, distinct
compact-source universe, and empty-source obstruction.
-/

noncomputable section
open CategoryTheory
open scoped Topology Simplicial unitInterval
universe u v
namespace Quillen.Tests.FiniteNullhomotopy

/-- An empty space cannot pass even the complete boundary-nullhomotopy test. -/
theorem empty_boundary_condition_impossible {X : Type u} [TopologicalSpace X] [IsEmpty X] :
    ¬ (∀ n : ℕ, ∀ a : C(CubicalTests.boundary.{u} n, X), a.Nullhomotopic) := by
  intro h
  have : IsEmpty PUnit.{u + 1} :=
    (isWeakHomotopyEquivalence_toPoint_of_boundary_nullhomotopic h).isEmpty_target
  exact isEmptyElim (PUnit.unit : PUnit.{u + 1})

/-- Finite nullhomotopies extend the prescribed boundary literally. -/
theorem extend_original_boundary {S : SSet.{u}}
    (h : ∀ A : S.Subcomplex, SSet.Finite A → (SSet.toTop.map A.ι).hom.Nullhomotopic)
    (n : ℕ) (a : C(CubicalTests.boundary.{u} n, |S|)) :
    ∃ c : C(CubicalTests.cube.{u} n, |S|),
      c.comp (CubicalTests.boundaryInclusion n).hom = a := by
  let : CompactSpace (CubicalTests.boundaryPresentation.{u} n).space :=
    (CubicalTests.boundaryPresentation n).compact
  let : CompactSpace (CubicalTests.boundary.{u} n) :=
    (CubicalTests.boundaryPresentationHomeomorph n).compactSpace
  exact exists_extend_of_nullhomotopic (CubicalTests.boundaryInclusion n)
    (CubicalTests.boundaryInclusion_hep n) a (realization_compactMap_nullhomotopic h a)

/-- All degrees, including the ungrouped zeroth set, use the original map. -/
theorem original_homotopy_maps_bijective {S : SSet.{u}}
    (h : ∀ A : S.Subcomplex, SSet.Finite A → (SSet.toTop.map A.ι).hom.Nullhomotopic)
    (x : |S|) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (ContinuousMap.const |S| (PUnit.unit : PUnit.{u + 1})) (x := x) rfl) :=
  (realization_toPoint_isWeakHomotopyEquivalence_of_finite_nullhomotopic h).homotopy_bijective x n

/-- A genuine global contraction supplies the finite tests, without requiring
that contraction to fix the chosen point. -/
theorem contractible_realization {S : SSet.{u}} [ContractibleSpace |S|] :
    IsWeakHomotopyEquivalence (ContinuousMap.const |S| (PUnit.unit : PUnit.{u + 1})) :=
  realization_toPoint_isWeakHomotopyEquivalence_of_finite_nullhomotopic
    (fun A _ => (id_nullhomotopic |S|).comp_left (SSet.toTop.map A.ι).hom)

/-- The compact source can occupy an independent universe. -/
theorem compact_source_universe {S : SSet.{u}}
    (h : ∀ A : S.Subcomplex, SSet.Finite A → (SSet.toTop.map A.ι).hom.Nullhomotopic)
    {T : Type v} [TopologicalSpace T] [CompactSpace T] (f : C(T, |S|)) :
    f.Nullhomotopic := realization_compactMap_nullhomotopic h f

end Quillen.Tests.FiniteNullhomotopy
