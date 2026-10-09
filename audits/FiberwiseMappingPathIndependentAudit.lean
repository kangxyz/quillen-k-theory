import Quillen.Topology.FiberwiseMappingPath.Restriction
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.FiberwiseMappingPath.Basic,
    `Quillen.Topology.FiberwiseMappingPath.Restriction]
  let mut counts : Array Nat := #[0,0]
  let mut total : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    total := total+1
    counts := counts.modify i (·+1)
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for i in [:targets.size] do
    unless counts[i]! > 0 do throwError "Missing origin {targets[i]!}"
    logInfo m!"ORIGIN_COUNT {targets[i]!}: {counts[i]!}"
  unless total == 70 && counts == #[35,35] do
    throwError "Expected fixed70 = 35+35, found {total}: {counts}"
  logInfo m!"FIXED70 PASSED {total}: {counts}"

noncomputable section
open scoped Topology unitInterval
open unitInterval
open Quillen.FiberwiseMappingPath
universe u v w
variable {E : Type u} {F : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  (q : C(F,B)) (f : C(E,F)) (U : Set B)

-- All three space universes remain independent throughout these consumers.
example : ContinuousMap.HomotopyEquiv E (Space q f) := inclusionHomotopyEquiv q f
example : (inclusionHomotopyEquiv q f).toFun = inclusion q f := rfl
example : (inclusionHomotopyEquiv q f).invFun = source q f := rfl
example (x : E) (s : I) : (inclusion q f x).val.2 s = f x := rfl
example : (source q f).comp (inclusion q f) = .id E := rfl
example : (endpoint q f).comp (inclusion q f) = f := rfl
example (z : Space q f) : q (endpoint q f z) = q (f (source q f z)) := z.property.2 1
example (t : I) (z : Space q f) : source q f (contraction q f (t,z)) = source q f z := rfl
example (t s : I) (z : Space q f) : (contraction q f (t,z)).val.2 s = z.val.2 (σ t * s) := rfl
example (t : I) (x : E) : contraction q f (t,inclusion q f x) = inclusion q f x := rfl
example (z : Space q f) : contraction q f (0,z) = z := (contraction q f).map_zero_left z
example (z : Space q f) : contraction q f (1,z) = inclusion q f (source q f z) :=
  (contraction q f).map_one_left z
example (t : I) (z : Space q f) :
    q (endpoint q f (contraction q f (t,z))) = q (endpoint q f z) := contraction_base q f t z

example : RestrictedSpace q f U ≃ₜ Space (restrictedProjection q U) (restrictedMap q f U) :=
  restrictionHomeomorph q f U
example (z : RestrictedSpace q f U) :
    (source (restrictedProjection q U) (restrictedMap q f U)
      (restrictionHomeomorph q f U z)).val = source q f z.val := rfl
example (z : RestrictedSpace q f U) (t : I) :
    ((restrictionHomeomorph q f U z).val.2 t).val = z.val.val.2 t := rfl
example (z : Space (restrictedProjection q U) (restrictedMap q f U)) (t : I) :
    ((restrictionHomeomorph q f U).symm z).val.val.2 t = (z.val.2 t).val := rfl
example : (endpoint (restrictedProjection q U) (restrictedMap q f U)).comp
    (restrictionHomeomorph q f U).toHomotopyEquiv.toFun = restrictedEndpoint q f U := rfl
example (z : RestrictedSpace q f U) :
    (restrictionHomeomorph q f U).symm (restrictionHomeomorph q f U z) = z :=
  (restrictionHomeomorph q f U).symm_apply_apply z
example (z : Space (restrictedProjection q U) (restrictedMap q f U)) :
    restrictionHomeomorph q f U ((restrictionHomeomorph q f U).symm z) = z :=
  (restrictionHomeomorph q f U).apply_symm_apply z

example : q.comp (endpoint q f) = (q.comp f).comp (source q f) := endpoint_base q f
example : (source q f).comp (inclusion q f) |>.Homotopic (ContinuousMap.id E) :=
  (inclusionHomotopyEquiv q f).left_inv
example : (inclusion q f).comp (source q f) |>.Homotopic (ContinuousMap.id (Space q f)) :=
  (inclusionHomotopyEquiv q f).right_inv

-- Stronger full-coordinate tests, including compatibility of section and scaling.
example (x : RestrictedSource q f U) :
    restrictionHomeomorph q f U ⟨inclusion q f x.val,x.property⟩ =
      inclusion (restrictedProjection q U) (restrictedMap q f U) x := rfl
example (z : RestrictedSpace q f U) (t : I) :
    restrictionHomeomorph q f U
      ⟨contraction q f (t,z.val),by rw [contraction_base]; exact z.property⟩ =
      contraction (restrictedProjection q U) (restrictedMap q f U)
        (t,restrictionHomeomorph q f U z) := rfl
example (z : Space (restrictedProjection q U) (restrictedMap q f U)) (t : I) :
    ((restrictionHomeomorph q f U).symm
      (contraction (restrictedProjection q U) (restrictedMap q f U) (t,z))).val =
        contraction q f (t,((restrictionHomeomorph q f U).symm z).val) := rfl
example (z : Space (restrictedProjection q U) (restrictedMap q f U)) :
    endpoint q f ((restrictionHomeomorph q f U).symm z).val =
      (endpoint (restrictedProjection q U) (restrictedMap q f U) z).val := rfl
example : IsEmpty (RestrictedSpace q f (∅ : Set B)) := ⟨fun z ↦ z.property⟩
example (z : Space q f) (s : I) :
    ((restrictionHomeomorph q f Set.univ ⟨z,Set.mem_univ _⟩).val.2 s).val = z.val.2 s := rfl
