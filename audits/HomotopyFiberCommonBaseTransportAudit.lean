import Quillen.Topology.HomotopyFiber.CommonBaseSquareTransport
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Topology.HomotopyFiber.CommonBaseSquareTransport
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
  unless count == 10 do throwError "Expected10 original origins, got {count}"
  logInfo m!"Audited all common-base transport origins: {count}"
noncomputable section
open Quillen
open scoped Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Maps
variable {F X Y B : Type u} [TopologicalSpace F] [TopologicalSpace X]
  [TopologicalSpace Y] [TopologicalSpace B]
  (q : C(Y,B)) (j : C(X,Y)) (b : B) (f : C(F,Y))
  (k : C(F,HomotopyFiber q b)) (hk : (HomotopyFiber.projection q b).comp k = f)
example (z : HomotopyPullback f j) :
    (HomotopyFiber.fiberModelPullbackMap q j b f k hk z).1.1 = z.1.1 := rfl
example (z : HomotopyPullback f j) :
    (HomotopyFiber.fiberModelPullbackMap q j b f k hk z).1.2.1 = k z.1.2.1 := rfl
example (z : HomotopyPullback f j) :
    (HomotopyFiber.fiberModelPullbackMap q j b f k hk z).1.2.2 = z.1.2.2 := rfl
example : HomotopyFiber.fiberModelPullbackMap q j b ((HomotopyFiber.projection q b).comp k) k rfl =
    HomotopyPullback.sourceMap j (HomotopyFiber.projection q b) k := rfl
example (h : IsWeakHomotopyEquivalence k) :
    IsWeakHomotopyEquivalence (HomotopyFiber.fiberModelPullbackMap q j b f k hk) :=
  HomotopyFiber.fiberModelPullbackMap_isWeakHomotopyEquivalence q j b f k hk h
end Maps
section Comparison
variable {A F X Y B : Type u} [TopologicalSpace A] [TopologicalSpace F]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
  (p : C(X,B)) (q : C(Y,B)) (j : C(X,Y)) (sq : q.comp j = p) (b : B)
  (a : C(A,X)) (f : C(F,Y)) (i : C(A,F)) (w : f.comp i = j.comp a)
  (k₀ : C(A,HomotopyFiber p b)) (k₁ : C(F,HomotopyFiber q b))
  (h₀ : (HomotopyFiber.projection p b).comp k₀ = a)
  (h₁ : (HomotopyFiber.projection q b).comp k₁ = f)
  (hc : (HomotopyFiber.mapOver p q j sq b).comp k₀ = k₁.comp i)
example : (HomotopyFiber.fiberModelPullbackMap q j b f k₁ h₁).comp
    (HomotopyPullback.comparison f j a i w) =
      (HomotopyFiber.commonBaseComparison p q j sq b).comp k₀ :=
  HomotopyFiber.fiberModelComparison_factorization p q j sq b a f i w k₀ k₁ h₀ h₁ hc
example (hk₀ : IsWeakHomotopyEquivalence k₀) (hk₁ : IsWeakHomotopyEquivalence k₁) :
    IsWeakHomotopyEquivalence (HomotopyPullback.comparison f j a i w) :=
  HomotopyFiber.fiberModelComparison_isWeakHomotopyEquivalence
    p q j sq b a f i w k₀ k₁ h₀ h₁ hc hk₀ hk₁
end Comparison
section ActualFiberModels
variable {X Y B : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
  (p : C(X,B)) (q : C(Y,B)) (j : C(X,Y)) (sq : q.comp j = p) (b : B)
-- The actual fibers supply both weak model maps unconditionally.
example : IsWeakHomotopyEquivalence (HomotopyFiber.commonBaseComparison p q j sq b) := by
  exact HomotopyFiber.fiberModelComparison_isWeakHomotopyEquivalence p q j sq b
    (HomotopyFiber.projection p b) (HomotopyFiber.projection q b)
    (HomotopyFiber.mapOver p q j sq b) rfl
    (ContinuousMap.id _) (ContinuousMap.id _) rfl rfl rfl
    (isWeakHomotopyEquivalence_id _) (isWeakHomotopyEquivalence_id _)
end ActualFiberModels
