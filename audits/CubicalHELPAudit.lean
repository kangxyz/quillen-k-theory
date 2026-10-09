import Quillen.Library
import Quillen.Topology.HELP.FiberwiseWeakEquivalence
import Quillen.Topology.HomotopyFiber.BasepointHELP
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.HELP.CubeBoundary,
    `Quillen.Topology.HELP.CubicalLifting, `Quillen.Topology.HELP.FiberwiseWeakEquivalence]
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
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}: {axs}"
  unless seen.size == 3 do throwError "Missing cubical source origin"
  unless count == 65 do throwError "Expected 65 cubical HELP origins, found {count}"
  logInfo m!"Audited all {count} cubical HELP origins."
noncomputable section
open CategoryTheory Quillen Quillen.CubicalTests
open scoped Topology unitInterval
universe u
section Boundary
example (n : ℕ) : CompactSpace (boundaryPresentation.{u} n).space :=
  (boundaryPresentation n).compact
example (n : ℕ) : TheoremA.homotopyExtensionProperty (boundaryPresentation.{u} n).map :=
  (boundaryPresentation n).hep
example (n : ℕ) : Set.range (boundaryPresentation.{u} n).map =
    {z : cube.{u} n | z.down ∈ Cube.boundary (Fin n)} := boundaryPresentation_range n
example : (boundaryPresentation.{u} 0).space = TopCat.of PEmpty.{u+1} := rfl
example (n : ℕ) : (boundaryPresentation.{u} (n+1)).space =
    TheoremA.CylinderBoundary (boundaryPresentation.{u} n).map := rfl
example (n : ℕ) : (boundaryPresentation.{u} (n+1)).map =
    TheoremA.cylinderBoundaryMap (boundaryPresentation.{u} n).map ≫
      (TopCat.isoOfHomeo (stepHomeomorph n)).hom := rfl
example (n : ℕ) (t : unitInterval) (z : cube.{u} n) (j : Fin n) :
    (contraction n (t,z)).down j = unitInterval.symm t * z.down j := rfl
example (n : ℕ) (z : cube.{u} n × unitInterval) :
    (stepHomeomorph n z).down = Fin.cons z.2 z.1.down := rfl
end Boundary
section Generic
variable {E F : Type u} [TopologicalSpace E] [TopologicalSpace F]
    (f : C(E,F)) (hf : ContractedStrictHELP f)
example : IsWeakHomotopyEquivalence f := hf.isWeakHomotopyEquivalence
example (y : F) : ∃ x, Joined (f x) y := hf.component_surjective y
example (x : E) (n : ℕ) : Function.Bijective
    (homotopyGroupMap (N := Fin n) f (x := x) rfl) :=
  hf.isWeakHomotopyEquivalence.homotopy_bijective x n
example (x : E) : Function.Bijective
    (homotopyGroupMap (N := Fin 0) f (x := x) rfl) :=
  hf.isWeakHomotopyEquivalence.homotopy_bijective x 0
example [IsEmpty E] : IsEmpty F := hf.isWeakHomotopyEquivalence.isEmpty_target
example (h : CompactHomotopyExtensionLiftingProperty f) : IsWeakHomotopyEquivalence f :=
  h.isWeakHomotopyEquivalence
end Generic
section Fibers
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b, CompactHomotopyExtensionLiftingProperty (HomotopyFiber.strictMapOver p q f sq b))
example : ContractedStrictHELP f := contractedStrictHELP_of_fiberHELP p q f sq hp hq hf
example : IsWeakHomotopyEquivalence f := isWeakHomotopyEquivalence_of_fiberHELP p q f sq hp hq hf
example (x : E) (n : ℕ) : Function.Bijective
    (homotopyGroupMap (N := Fin n) f (x := x) rfl) :=
  (isWeakHomotopyEquivalence_of_fiberHELP p q f sq hp hq hf).homotopy_bijective x n
example (x : E) : Function.Bijective
    (homotopyGroupMap (N := Fin 0) f (x := x) rfl) :=
  (isWeakHomotopyEquivalence_of_fiberHELP p q f sq hp hq hf).homotopy_bijective x 0
example [IsEmpty E] : IsEmpty F :=
  (isWeakHomotopyEquivalence_of_fiberHELP p q f sq hp hq hf).isEmpty_target
example (y : F) : ∃ x, Joined (f x) y :=
  (isWeakHomotopyEquivalence_of_fiberHELP p q f sq hp hq hf).component_surjective y
end Fibers
section ChosenFiber
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (b₀ : B) (hb : ∀ b : B, Joined b₀ b)
    (hf : CompactHomotopyExtensionLiftingProperty (HomotopyFiber.strictMapOver p q f sq b₀))
example : IsWeakHomotopyEquivalence f :=
  isWeakHomotopyEquivalence_of_fiberHELP p q f sq hp hq
    (fun b ↦ HomotopyFiber.compactHELP_strictMapOver_of_joined p q f sq hp hq (hb b) hf)
end ChosenFiber
