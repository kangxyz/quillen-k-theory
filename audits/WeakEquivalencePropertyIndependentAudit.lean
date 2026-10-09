import Lean.Util.CollectAxioms
import Quillen.Topology.HomotopyGroups.WeakEquivalenceProperty
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == `Quillen.Topology.HomotopyGroups.WeakEquivalenceProperty do continue
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}"
  unless count == 15 do throwError "Expected exactly 15 origins, found {count}"
  logInfo m!"Audited all {count} empty-aware weak-equivalence declarations."
noncomputable section
open Quillen
open scoped Topology
universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (f : C(X,Y)) (g : C(Y,Z))
example (h : IsWeakHomotopyEquivalence f) (y : Y) : ∃ x : X, Joined (f x) y :=
  h.component_surjective y
example (h : IsWeakHomotopyEquivalence f) (x : X) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) f (x := x) rfl) := h.homotopy_bijective x 0
example (h : IsWeakHomotopyEquivalence f) [IsEmpty X] : IsEmpty Y := h.isEmpty_target
example (h : IsWeakHomotopyEquivalence f) [IsEmpty X] [Nonempty Y] : False := by
  let := h.isEmpty_target
  exact isEmptyElim (Classical.choice (inferInstance : Nonempty Y))
example (hf : IsWeakHomotopyEquivalence f) (hg : IsWeakHomotopyEquivalence g) :
    IsWeakHomotopyEquivalence (g.comp f) := hg.comp hf
example (x : X) (h : Function.Surjective (homotopyGroupMap (N := Fin 0) f (x := x) rfl)) :
    ∀ y : Y, ∃ x' : X, Joined (f x') y := component_surjective_of_homotopyGroupMap_zero_surjective f x h
example (e : ContinuousMap.HomotopyEquiv X Y) : IsWeakHomotopyEquivalence e.toFun :=
  isWeakHomotopyEquivalence_of_homotopyEquiv e
example : IsWeakHomotopyEquivalence (ContinuousMap.id X) := isWeakHomotopyEquivalence_id X
example [PathConnectedSpace X] [PathConnectedSpace Y] (x : X)
    (h : ∀ n, Function.Bijective (piMap n f (x := x) rfl)) : IsWeakHomotopyEquivalence f :=
  isWeakHomotopyEquivalence_of_connected f x h
