import Quillen.Topology.FiberwiseMappingPath.Restriction
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.FiberwiseMappingPath.Basic,
    `Quillen.Topology.FiberwiseMappingPath.Restriction]
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
  unless seen.size == 2 do throwError "Missing vertical-model origin"
  unless count == 70 do throwError "Expected 70 vertical-model origins, found {count}"
  logInfo m!"Audited all {count} vertical-model origins."
noncomputable section
open Quillen
open scoped Topology unitInterval
universe u v w
namespace VerticalModelConsumers
open FiberwiseMappingPath
variable {E : Type u} {F : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  (q : C(F,B)) (f : C(E,F))
example : (endpoint q f).comp (inclusion q f) = f := rfl
example : (source q f).comp (inclusion q f) = ContinuousMap.id E := rfl
example : q.comp (endpoint q f) = (q.comp f).comp (source q f) := endpoint_base q f
example : (inclusionHomotopyEquiv q f).toFun = inclusion q f := rfl
example : (inclusionHomotopyEquiv q f).invFun = source q f := rfl
example : (source q f).comp (inclusion q f) |>.Homotopic (ContinuousMap.id E) :=
  (inclusionHomotopyEquiv q f).left_inv
example : (inclusion q f).comp (source q f) |>.Homotopic (ContinuousMap.id (Space q f)) :=
  (inclusionHomotopyEquiv q f).right_inv
example (t s : unitInterval) (x : Space q f) :
    (contraction q f (t,x)).val.2 s = x.val.2 (unitInterval.symm t * s) := rfl
example (t : unitInterval) (x : E) : contraction q f (t,inclusion q f x) = inclusion q f x := rfl
example (t : unitInterval) (x : Space q f) :
    q (endpoint q f (contraction q f (t,x))) = q (endpoint q f x) := contraction_base q f t x
variable (U : Set B)
example : (endpoint (restrictedProjection q U) (restrictedMap q f U)).comp
    (restrictionHomeomorph q f U).toHomotopyEquiv.toFun = restrictedEndpoint q f U := rfl
example (x : RestrictedSpace q f U) (t : unitInterval) :
    ((restrictionHomeomorph q f U x).val.2 t).val = x.val.val.2 t := rfl
example (x : Space (restrictedProjection q U) (restrictedMap q f U)) (t : unitInterval) :
    ((restrictionHomeomorph q f U).symm x).val.val.2 t = (x.val.2 t).val := rfl
example (x : RestrictedSpace q f U) :
    (restrictionHomeomorph q f U).symm (restrictionHomeomorph q f U x) = x :=
  (restrictionHomeomorph q f U).symm_apply_apply x
example (x : Space (restrictedProjection q U) (restrictedMap q f U)) :
    restrictionHomeomorph q f U ((restrictionHomeomorph q f U).symm x) = x :=
  (restrictionHomeomorph q f U).apply_symm_apply x
end VerticalModelConsumers
