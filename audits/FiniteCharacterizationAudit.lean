import Quillen.Topology.HELP.FiniteCharacterization
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Topology.HELP.FiniteCharacterization
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some i := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[i.toNat]! == target do continue
    count := count + 1
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count == 4 do throwError "Expected 4 original declarations, got {count}"
  logInfo m!"Audited all original finite-characterization declarations: {count}"
noncomputable section
open Quillen
open scoped Topology
universe u
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X,Y))
example : IsWeakHomotopyEquivalence f ↔
    CubicalSubdivision.BoundaryLifting (MappingPath.endpoint f) :=
  isWeakHomotopyEquivalence_iff_mappingPath_boundaryLifting f
example : IsWeakHomotopyEquivalence f ↔ FiniteCubeHELP f :=
  isWeakHomotopyEquivalence_iff_finiteCubeHELP f
example (hf : FiniteCubeHELP f) : IsWeakHomotopyEquivalence f :=
  (isWeakHomotopyEquivalence_iff_finiteCubeHELP f).mpr hf
example (hf : IsWeakHomotopyEquivalence f) (n : ℕ)
    (a : C(CubicalTests.boundary.{u} n,X)) (b : C(CubicalTests.cube.{u} n,Y))
    (H : (f.comp a).Homotopy (b.comp (CubicalTests.boundaryInclusion n).hom)) :
    ∃ c : C(CubicalTests.cube.{u} n,X), c.comp (CubicalTests.boundaryInclusion n).hom = a ∧
      ∃ K : (f.comp c).Homotopy b,
        ∀ (t : unitInterval) (z : CubicalTests.boundary.{u} n), K (t,z.val) = H (t,z) :=
  (isWeakHomotopyEquivalence_iff_finiteCubeHELP f).mp hf n a b H
example : FiniteCubeHELP (ContinuousMap.id X) :=
  (isWeakHomotopyEquivalence_iff_finiteCubeHELP _).mp (isWeakHomotopyEquivalence_id X)
example [IsEmpty X] [Nonempty Y] : ¬ FiniteCubeHELP f := by
  intro hf
  have hw := (isWeakHomotopyEquivalence_iff_finiteCubeHELP f).mpr hf
  obtain ⟨x,_⟩ := hw.component_surjective (Classical.choice (inferInstance : Nonempty Y))
  exact isEmptyElim x
example (hf : FiniteCubeHELP f) (n : ℕ)
    (a : C(CubicalSubdivision.Boundary n,MappingPath f))
    (b : C(CubicalSubdivision.Cube n,Y))
    (h : ∀ z : CubicalSubdivision.Boundary n,MappingPath.endpoint f (a z) = b z) :
    ∃ c : C(CubicalSubdivision.Cube n,MappingPath f),
      (∀ z : CubicalSubdivision.Boundary n,c z = a z) ∧
        (MappingPath.endpoint f).comp c = b :=
  hf.mappingPath_boundaryLifting n a b h
example (hf : FiniteCubeHELP f) : Function.Surjective (MappingPath.endpoint f) :=
  hf.mappingPath_boundaryLifting.surjective
