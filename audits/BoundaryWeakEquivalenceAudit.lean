import Quillen.Library
import Quillen.Topology.CubicalSubdivision.BoundaryWeakEquivalence
import Quillen.Topology.CubicalSubdivision.LocalLifting
import Quillen.Topology.CubicalSubdivision.FiberBoundaryLifting
import Quillen.Waldhausen.Fibration.RelativeRows.CubicalLifting
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Topology.CubicalSubdivision.BoundaryWeakEquivalence
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == target do continue
    count := count + 1
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axs}"
  unless count == 6 do throwError "Expected 6 finite-boundary weak origins, found {count}"
  logInfo m!"Audited all {count} finite-boundary weak origins."
noncomputable section
open CategoryTheory Quillen Quillen.CubicalSubdivision
open scoped Topology unitInterval Simplicial
universe u v w
section Generic
variable {E : Type u} {F : Type v} [TopologicalSpace E] [TopologicalSpace F]
    (f : C(E,F)) (hf : BoundaryLifting f)
example : IsWeakHomotopyEquivalence f := hf.isWeakHomotopyEquivalence
example : Function.Surjective f := hf.surjective
example (y : F) : ∃ x, Joined (f x) y := hf.isWeakHomotopyEquivalence.component_surjective y
example (x : E) (n : ℕ) : Function.Surjective (homotopyGroupMap (N := Fin n) f (x := x) rfl) :=
  hf.homotopy_surjective x n
example (x : E) (n : ℕ) : Function.Injective (homotopyGroupMap (N := Fin n) f (x := x) rfl) :=
  hf.homotopy_injective x n
example (x : E) (n : ℕ) : Function.Bijective (homotopyGroupMap (N := Fin n) f (x := x) rfl) :=
  hf.isWeakHomotopyEquivalence.homotopy_bijective x n
example (x : E) : Function.Bijective (homotopyGroupMap (N := Fin 0) f (x := x) rfl) :=
  hf.isWeakHomotopyEquivalence.homotopy_bijective x 0
example [IsEmpty E] : IsEmpty F := hf.isWeakHomotopyEquivalence.isEmpty_target
example (n : ℕ) (a : C((CubicalTests.boundaryPresentation.{w} n).space,E))
    (b : C(CubicalTests.cube.{w} n,F))
    (hab : ∀ z,f (a z) = b ((CubicalTests.boundaryPresentation n).map z)) :
    ∃ c : C(CubicalTests.cube.{w} n,E),
      (∀ z,c ((CubicalTests.boundaryPresentation n).map z) = a z) ∧ f.comp c = b :=
  hf.presentation n a b hab
example (n : ℕ)
    (a : C(TheoremA.CylinderBoundary (CubicalTests.boundaryPresentation.{w} n).map,E))
    (b : C(CubicalTests.cube.{w} n × unitInterval,F))
    (hab : ∀ z,f (a z) = b (TheoremA.cylinderBoundaryMap (CubicalTests.boundaryPresentation n).map z)) :
    ∃ c : C(CubicalTests.cube.{w} n × unitInterval,E),
      (∀ z,c (TheoremA.cylinderBoundaryMap (CubicalTests.boundaryPresentation n).map z) = a z) ∧
        f.comp c = b := hf.cylinder n a b hab
end Generic
example {E F : Type u} [TopologicalSpace E] [TopologicalSpace F] (f : C(E,F))
    (hf : ∀ n,HasLiftingProperty (CubicalTests.boundaryInclusion.{u} n) (TopCat.ofHom f)) :
    IsWeakHomotopyEquivalence f := (boundaryLifting_of_hasLiftingProperty f hf).isWeakHomotopyEquivalence
example {E : Type u} {F : Type v} [TopologicalSpace E] [TopologicalSpace F]
    (f : C(E,F)) {J : Type w} (U : J → Set F) (hU : ∀ j,IsOpen (U j))
    (hc : ∀ y,∃ j,y ∈ U j) (hl : ∀ j,BoundaryLifting (restriction f (U j))) :
    IsWeakHomotopyEquivalence f := (BoundaryLifting.of_open_cover f U hU hc hl).isWeakHomotopyEquivalence
example {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b,CompactHomotopyExtensionLiftingProperty (HomotopyFiber.strictMapOver p q f sq b)) :
    IsWeakHomotopyEquivalence (MappingPath.endpoint f) :=
  (MappingPath.endpoint_boundaryLifting_of_fiberHELP p q f sq hp hq hf).isWeakHomotopyEquivalence
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.Fibration.RelativeRows
example {C : Type u} [Category.{u} C] {V : Structure C}
    (N : NestedWeakEquivalences V) {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) :
    IsWeakHomotopyEquivalence (MappingPath.endpoint (rowNormalizedComparison N α)) :=
  (rowNormalizedComparison_endpoint_boundaryLifting N α).isWeakHomotopyEquivalence
example {C : Type u} [Category.{u} C] {V : Structure C}
    (N : NestedWeakEquivalences V) {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n)
    (x : MappingPath (rowNormalizedComparison N α)) :
    Function.Bijective (homotopyGroupMap (N := Fin 0)
      (MappingPath.endpoint (rowNormalizedComparison N α)) (x := x) rfl) :=
  (rowNormalizedComparison_endpoint_boundaryLifting N α).isWeakHomotopyEquivalence.homotopy_bijective x 0
example {E F : Type u} [TopologicalSpace E] [TopologicalSpace F]
    (f : C(E,F)) (hf : BoundaryLifting (MappingPath.endpoint f)) : IsWeakHomotopyEquivalence f :=
  hf.isWeakHomotopyEquivalence.comp
    (isWeakHomotopyEquivalence_of_homotopyEquiv (MappingPath.inclusionHomotopyEquiv f))
