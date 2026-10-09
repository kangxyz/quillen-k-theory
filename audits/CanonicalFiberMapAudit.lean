import Quillen.Waldhausen.Fibration.CanonicalFiberMap
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Waldhausen.Fibration.CanonicalFiberMap
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless origin == target do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count == 24 do throwError "Expected 24 canonical fiber-map origins, got {count}"
  logInfo m!"Audited all {count} canonical fiber-map origins."
noncomputable section
open CategoryTheory Quillen Quillen.Waldhausen Fibration
open scoped Topology
universe u v
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
example : C((acyclicStructure N).Delooping, HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint) :=
  canonicalFiberMap N
example : (HomotopyFiber.projection (changeWeakMap N) N.coarse.kBasepoint).comp
    (canonicalFiberMap N) = (deloopingMap (acyclicInclusion_exact N)).hom := rfl
example : canonicalFiberMap N (acyclicStructure N).kBasepoint =
    HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint V.kBasepoint
      (changeWeakMap_basepoint N) := canonicalFiberMap_basepoint N
example : (KMap (changeWeak_exact N) 0).comp (KMap (acyclicInclusion_exact N) 0) = 1 :=
  changeWeak_KMap_comp_acyclic N 0
example : (piMap 0 (HomotopyFiber.projection (changeWeakMap N) N.coarse.kBasepoint)
      (HomotopyFiber.projection_basepoint _ _ V.kBasepoint (changeWeakMap_basepoint N))).comp
      (canonicalFiberKMap N 0) = KMap (acyclicInclusion_exact N) 0 :=
  canonicalFiberKMap_projection N 0
