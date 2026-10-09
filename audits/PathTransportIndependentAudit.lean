import Quillen.Topology.HomotopyGroups.PathTransport
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let wanted := `Quillen.Topology.HomotopyGroups.PathTransport
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == wanted do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count == 28 do throwError "Expected 28 PathTransport origins, got {count}"
  logInfo m!"Audited all {count} PathTransport declaration origins."

noncomputable section
open scoped Topology unitInterval
open Quillen
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {x₀ x₁ : X} (γ : Path x₀ x₁) (f : C(X, Y)) (n : ℕ)

example (t : unitInterval) :
    (freePathEvaluationHomotopyEquiv X t).toFun = freePathEvaluation X t := rfl
example (t : unitInterval) :
    (freePathEvaluationHomotopyEquiv X t).invFun = ContinuousMap.const' := rfl
example (t : unitInterval) (p : C(unitInterval, X)) :
    freePathEvaluation X t p = p t := rfl
example (p : C(unitInterval, X)) : freePathPostcomp f p = f.comp p := rfl
example (t : unitInterval) :
    (freePathEvaluation Y t).comp (freePathPostcomp f) = f.comp (freePathEvaluation X t) := rfl
example (a : HomotopyGroup.Pi n C(unitInterval, X) γ.toContinuousMap) :
    pathStartEquiv γ n a = homotopyGroupMap (freePathEvaluation X 0) γ.source a := rfl
example (a : HomotopyGroup.Pi n C(unitInterval, X) γ.toContinuousMap) :
    pathEndEquiv γ n a = homotopyGroupMap (freePathEvaluation X 1) γ.target a := rfl
example : pathTransport γ n = (pathStartEquiv γ n).symm.trans (pathEndEquiv γ n) := rfl
example : HomotopyGroup (Fin n) X x₀ ≃ HomotopyGroup (Fin n) X x₁ := pathTransport γ n
example (a : HomotopyGroup (Fin n) X x₀) :
    pathTransport (γ.map f.continuous) n (homotopyGroupMap f rfl a) =
      homotopyGroupMap f rfl (pathTransport γ n a) := pathTransport_naturality f γ n a
example : Function.Injective (homotopyGroupMap (N := Fin n) f (x := x₀) rfl) ↔
    Function.Injective (homotopyGroupMap (N := Fin n) f (x := x₁) rfl) :=
  homotopyGroupMap_injective_iff_of_path f γ n
example : Function.Surjective (homotopyGroupMap (N := Fin n) f (x := x₀) rfl) ↔
    Function.Surjective (homotopyGroupMap (N := Fin n) f (x := x₁) rfl) :=
  homotopyGroupMap_surjective_iff_of_path f γ n
example : Function.Bijective (homotopyGroupMap (N := Fin n) f (x := x₀) rfl) ↔
    Function.Bijective (homotopyGroupMap (N := Fin n) f (x := x₁) rfl) :=
  homotopyGroupMap_bijective_iff_of_path f γ n
example (a : HomotopyGroup (Fin 0) X x₀) :
    pathTransport (γ.map f.continuous) 0 (homotopyGroupMap f rfl a) =
      homotopyGroupMap f rfl (pathTransport γ 0 a) := pathTransport_naturality f γ 0 a
example : Function.Bijective (homotopyGroupMap (N := Fin 0) f (x := x₀) rfl) ↔
    Function.Bijective (homotopyGroupMap (N := Fin 0) f (x := x₁) rfl) :=
  homotopyGroupMap_bijective_iff_of_path f γ 0
example : pathTransport γ 0 (Quotient.mk' GenLoop.const) = Quotient.mk' GenLoop.const :=
  pathTransport_const γ 0
example : pathTransport (Path.refl x₀) 0 = Equiv.refl _ := pathTransport_refl x₀ 0
example (h : Joined x₀ x₁) :
    Function.Bijective (homotopyGroupMap (N := Fin n) f (x := x₀) rfl) ↔
      Function.Bijective (homotopyGroupMap (N := Fin n) f (x := x₁) rfl) :=
  homotopyGroupMap_bijective_iff_of_joined f h n
example [PathConnectedSpace X]
    (h : Function.Bijective (homotopyGroupMap (N := Fin n) f (x := x₀) rfl)) :
    ∀ x₁ : X, Function.Bijective (homotopyGroupMap (N := Fin n) f (x := x₁) rfl) :=
  homotopyGroupMap_bijective_at_all_points f x₀ n h
