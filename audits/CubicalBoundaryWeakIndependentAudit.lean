import Quillen.Library
import Quillen.Topology.CubicalSubdivision.BoundaryWeakEquivalence
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.CubicalSubdivision.BoundaryWeakEquivalence]
  let mut count : Nat := 0
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless targets.contains origin do continue
    count := count + 1
    seen := seen.insert origin
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}: {axs}"
  unless seen.size == 1 do throwError "Missing boundary-weak-equivalence origin"
  unless count == 6 do throwError "Expected 6 boundary-weak-equivalence origins, found {count}"
  logInfo m!"Audited all {count} boundary-weak-equivalence origins."
noncomputable section
open CategoryTheory Quillen Quillen.CubicalSubdivision
open scoped Topology unitInterval
universe u v w
variable {E : Type u} {F : Type v} [TopologicalSpace E] [TopologicalSpace F]
  (f : C(E,F)) (hf : BoundaryLifting f)
example : Function.Surjective f := hf.surjective
example (y : F) : ∃ x,f x = y := hf.surjective y
example [IsEmpty E] : IsEmpty F := ⟨fun y ↦ by obtain ⟨x,_⟩ := hf.surjective y; exact isEmptyElim x⟩
example : IsWeakHomotopyEquivalence f := hf.isWeakHomotopyEquivalence
example (y : F) : ∃ x,Joined (f x) y := hf.isWeakHomotopyEquivalence.component_surjective y
example (x : E) (n : ℕ) : Function.Surjective (homotopyGroupMap (N := Fin n) f (x := x) rfl) :=
  hf.homotopy_surjective x n
example (x : E) (n : ℕ) : Function.Injective (homotopyGroupMap (N := Fin n) f (x := x) rfl) :=
  hf.homotopy_injective x n
example (x : E) : Function.Bijective (homotopyGroupMap (N := Fin 0) f (x := x) rfl) :=
  hf.isWeakHomotopyEquivalence.homotopy_bijective x 0
example (x : E) (n : ℕ) : Function.Bijective (homotopyGroupMap (N := Fin n) f (x := x) rfl) :=
  ⟨hf.homotopy_injective x n,hf.homotopy_surjective x n⟩
example (n : ℕ) (a : C((CubicalTests.boundaryPresentation.{w} n).space,E))
    (b : C(CubicalTests.cube.{w} n,F))
    (h : ∀ z,f (a z) = b ((CubicalTests.boundaryPresentation n).map z)) :
    ∃ c : C(CubicalTests.cube.{w} n,E),
      (∀ z,c ((CubicalTests.boundaryPresentation n).map z) = a z) ∧ f.comp c = b :=
  hf.presentation n a b h
example (a : C((CubicalTests.boundaryPresentation.{w} 0).space,E))
    (b : C(CubicalTests.cube.{w} 0,F))
    (h : ∀ z,f (a z) = b ((CubicalTests.boundaryPresentation 0).map z)) :
    ∃ c : C(CubicalTests.cube.{w} 0,E),
      (∀ z,c ((CubicalTests.boundaryPresentation 0).map z) = a z) ∧ f.comp c = b :=
  hf.presentation 0 a b h
open Quillen.TheoremA
example (n : ℕ)
    (a : C(CylinderBoundary (CubicalTests.boundaryPresentation.{w} n).map,E))
    (b : C(CubicalTests.cube.{w} n × unitInterval,F))
    (h : ∀ z,f (a z) = b (cylinderBoundaryMap (CubicalTests.boundaryPresentation n).map z)) :
    ∃ c : C(CubicalTests.cube.{w} n × unitInterval,E),
      (∀ z,c (cylinderBoundaryMap (CubicalTests.boundaryPresentation n).map z) = a z) ∧
        f.comp c = b := hf.cylinder n a b h
example (a : C(CylinderBoundary (CubicalTests.boundaryPresentation.{w} 0).map,E))
    (b : C(CubicalTests.cube.{w} 0 × unitInterval,F))
    (h : ∀ z,f (a z) = b (cylinderBoundaryMap (CubicalTests.boundaryPresentation 0).map z)) :
    ∃ c : C(CubicalTests.cube.{w} 0 × unitInterval,E),
      (∀ z,c (cylinderBoundaryMap (CubicalTests.boundaryPresentation 0).map z) = a z) ∧
        f.comp c = b := hf.cylinder 0 a b h
