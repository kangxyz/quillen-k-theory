import Quillen

/-! Public consumers of finite HELP, using the original maps and full paths. -/
noncomputable section
open Quillen
open scoped Topology
universe u
namespace Consumer.FiniteHELP
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X,Y))

theorem weak_iff_full_finite : IsWeakHomotopyEquivalence f ↔ FiniteCubeHELP f :=
  isWeakHomotopyEquivalence_iff_finiteCubeHELP f

theorem original_endpoint_lifts (hf : IsWeakHomotopyEquivalence f) :
    CubicalSubdivision.BoundaryLifting (MappingPath.endpoint f) :=
  hf.mappingPath_endpoint_boundaryLifting

theorem original_boundary_track (hf : IsWeakHomotopyEquivalence f) (n : ℕ)
    (a : C(CubicalTests.boundary.{u} n,X)) (b : C(CubicalTests.cube.{u} n,Y))
    (H : (f.comp a).Homotopy (b.comp (CubicalTests.boundaryInclusion n).hom)) :
    ∃ c : C(CubicalTests.cube.{u} n,X), c.comp (CubicalTests.boundaryInclusion n).hom = a ∧
      ∃ K : (f.comp c).Homotopy b,
        ∀ (t : unitInterval) (z : CubicalTests.boundary.{u} n), K (t,z.val) = H (t,z) :=
  hf.cube_fullHELP n a b H

theorem original_zero_cube (hf : IsWeakHomotopyEquivalence f)
    (a : C(CubicalTests.boundary.{u} 0,X)) (b : C(CubicalTests.cube.{u} 0,Y))
    (H : (f.comp a).Homotopy (b.comp (CubicalTests.boundaryInclusion 0).hom)) :
    ∃ c : C(CubicalTests.cube.{u} 0,X), c.comp (CubicalTests.boundaryInclusion 0).hom = a ∧
      ∃ K : (f.comp c).Homotopy b,
        ∀ (t : unitInterval) (z : CubicalTests.boundary.{u} 0), K (t,z.val) = H (t,z) :=
  hf.cube_fullHELP 0 a b H

theorem identity_full_finite : FiniteCubeHELP (ContinuousMap.id X) :=
  (weak_iff_full_finite _).mp (isWeakHomotopyEquivalence_id X)

theorem empty_source_obstruction [IsEmpty X] [Nonempty Y] : ¬ FiniteCubeHELP f := by
  intro hf
  obtain ⟨x,_⟩ := ((weak_iff_full_finite f).mpr hf).component_surjective
    (Classical.choice (inferInstance : Nonempty Y))
  exact isEmptyElim x

end Consumer.FiniteHELP
