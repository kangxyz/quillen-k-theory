import Quillen.Topology.HomotopyFiber.ContractibleBaseHELP
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.HomotopyFiber.ContractibleBase,
    `Quillen.Topology.HomotopyFiber.ContractibleBaseHELP]
  let mut count : Nat := 0
  for origin in targets do
    let mut subtotal : Nat := 0
    for (name, _) in env.constants.toList do
      let some index := env.getModuleIdxFor? name | continue
      unless env.header.moduleNames[index.toNat]! == origin do continue
      count := count + 1
      subtotal := subtotal + 1
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{origin}: {name} depends on unsupported assumption {dependency}"
      logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
    logInfo m!"ORIGIN_COUNT {origin}: {subtotal}"
  unless count == 12 do throwError "Expected12 contracted-base origins, got {count}"
  unless count == 12 do throwError "Expected 12 contracted-base origins, got {count}"
  logInfo m!"Audited all {count} contracted-base origins."
noncomputable section
open scoped Topology unitInterval
universe u
namespace Quillen.HomotopyFiber
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
variable (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
  (b : B) (H : (ContinuousMap.id B).Homotopy (ContinuousMap.const B b))
example : (pointInclusionEquiv b H).toFun = ContinuousMap.const (ULift.{u} Unit) b := rfl
example : (pointInclusionEquiv b H).invFun = ContinuousMap.const B (⟨()⟩ : ULift.{u} Unit) := rfl
example : (projectionEquivOfContraction p b H).toFun = projection p b := rfl
example (x : HomotopyFiber p b) : (projectionEquivOfContraction p b H).toFun x = x.val.1 := rfl
example (hp : HomotopyLiftingProperty p) :
    (strictFiberEquivOfContraction p hp b H).toFun = strictFiberToSource p b := rfl
example (hp : HomotopyLiftingProperty p) (x : {x : E // p x = b}) :
    (strictFiberEquivOfContraction p hp b H).toFun x = x.val := rfl
example (hf : CompactHomotopyExtensionLiftingProperty (mapOver p q f sq b)) :
    CompactHomotopyExtensionLiftingProperty f := compactHELP_of_fiber_contraction p q f sq b H hf
example (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : CompactHomotopyExtensionLiftingProperty (strictMapOver p q f sq b)) :
    CompactHomotopyExtensionLiftingProperty f :=
  compactHELP_of_strictFiber_contraction p q f sq hp hq b H hf
end Quillen.HomotopyFiber

namespace Quillen.HomotopyFiber
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
variable (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    (b : B) (H : (ContinuousMap.id B).Homotopy (ContinuousMap.const B b))
example : (projection q b).comp (mapOver p q f sq b) = f.comp (projection p b) := rfl
example : (strictFiberToSource q b).comp (strictMapOver p q f sq b) =
    f.comp (strictFiberToSource p b) := rfl
example [IsEmpty E] : IsEmpty (HomotopyFiber p b) :=
  ⟨fun z ↦ isEmptyElim ((projectionEquivOfContraction p b H) z)⟩
example (x : E) : Nonempty (HomotopyFiber p b) :=
  ⟨(projectionEquivOfContraction p b H).invFun x⟩
example (z : HomotopyFiber p b) :
    (projectionEquivOfContraction p b H).toFun z = z.1.1 := rfl
end Quillen.HomotopyFiber
