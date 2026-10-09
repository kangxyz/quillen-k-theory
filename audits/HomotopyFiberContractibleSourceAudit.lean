import Quillen.Topology.HomotopyFiber.ContractibleSource
import Quillen.Waldhausen.Fibration.AllWeak.RelativeContractible
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Topology.HomotopyFiber.ContractibleSource
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == target do continue
    count := count + 1
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count == 25 do throwError "Expected25 origins, got {count}"
  logInfo m!"Audited all{count} original contractible-source declarations."

noncomputable section
open Quillen Quillen.HomotopyFiber
open scoped Topology unitInterval Simplicial
universe u v
section Generic
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ContractibleSpace X] (f : C(X,Y)) (y : Y) (x : X) (h : f x = y)
example : (ContinuousMap.id X).Homotopy (ContinuousMap.const X x) := contractibleSourceContraction x
example : (sourcePointEquiv x).toFun = ContinuousMap.const Unit x := rfl
example : (sourcePointEquiv x).invFun = ContinuousMap.const X () := rfl
example : HomotopyFiber (f.comp (ContinuousMap.const Unit x)) y ≃ₜ Path y y :=
  pointSourceFiberHomeomorph f y x h
example (γ : Path y y) : ((pointSourceFiberHomeomorph f y x h).symm γ).1.2 =
    γ.toContinuousMap := rfl
example : (loopInclusionEquivOfContractibleSource f y x h).toFun = loopInclusion f y x h :=
  loopInclusionEquivOfContractibleSource_toFun f y x h
example (γ : Path y y) : ((loopInclusionEquivOfContractibleSource f y x h) γ).1.1 = x := rfl
example (γ : Path y y) : ((loopInclusionEquivOfContractibleSource f y x h) γ).1.2 =
    γ.toContinuousMap := rfl
example : loopInclusionEquivOfContractibleSource f y x h (Path.refl y) =
    basepoint f y x h := rfl
example : Function.Bijective (homotopyGroupMap (N := Fin 0) (loopInclusion f y x h)
    (x := Path.refl y) (y := basepoint f y x h) rfl) :=
  loopInclusion_bijective_of_contractibleSource f y x h 0
example (n : ℕ) : Function.Bijective (homotopyGroupMap (N := Fin n) (loopInclusion f y x h)
    (x := Path.refl y) (y := basepoint f y x h) rfl) :=
  loopInclusion_bijective_of_contractibleSource f y x h n
end Generic
section ActualRelative
open CategoryTheory Waldhausen Waldhausen.Fibration
variable {C : Type u} [SmallCategory C] (W : Structure C)
example : let f := (SSet.toTop.map (TheoremA.diagonalMap (RelativeRows.tailSRows (AllWeak.nested W)))).hom
    let x := RelativeRows.totalBasepoint (AllWeak.nested W)
    ContinuousMap.HomotopyEquiv (Path (f x) (f x)) (HomotopyFiber f (f x)) :=
  loopInclusionEquivOfContractibleSource _ _ _ rfl
example : let f := (SSet.toTop.map (TheoremA.diagonalMap (RelativeRows.tailSRows (AllWeak.nested W)))).hom
    let x := RelativeRows.totalBasepoint (AllWeak.nested W)
    (loopInclusionEquivOfContractibleSource f (f x) x rfl).toFun = loopInclusion f (f x) x rfl :=
  loopInclusionEquivOfContractibleSource_toFun _ _ _ rfl
end ActualRelative
