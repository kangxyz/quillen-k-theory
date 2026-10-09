import Quillen.Topology.FiberwiseMappingPath.BaseChangeLifting
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.FiberwiseMappingPath.BaseChange,
    `Quillen.Topology.FiberwiseMappingPath.BaseChangeLifting]
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
  unless seen.size == 2 do throwError "Missing vertical-base-change origin"
  unless count == 34 do throwError "Expected 34 vertical-base-change origins, found {count}"
  logInfo m!"Audited all {count} vertical-base-change origins."
noncomputable section
open Quillen Quillen.FiberwiseMappingPath
open scoped Topology unitInterval
universe u v w z
variable {E : Type u} {F : Type v} {B : Type w} {T : Type z}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B] [TopologicalSpace T]
  (q : C(F,B)) (f : C(E,F)) (g : C(T,B))
example (x : BaseChangedSource q f g) : (baseChangedMap q f g x).val = (x.val.1,f x.val.2) := rfl
example (x : Space (baseChangedProjection q g) (baseChangedMap q f g)) (t : unitInterval) :
    (baseChangeHomeomorph q f g x).val.2.val.2 t = (x.val.2 t).val.2 := rfl
example (x : BaseChangedSpace q f g) (t : unitInterval) :
    (((baseChangeHomeomorph q f g).symm x).val.2 t).val = (x.val.1,x.val.2.val.2 t) := rfl
example (x : BaseChangedSpace q f g) :
    (endpoint (baseChangedProjection q g) (baseChangedMap q f g)
      ((baseChangeHomeomorph q f g).symm x)).val = (x.val.1,endpoint q f x.val.2) := rfl
example (x : Space (baseChangedProjection q g) (baseChangedMap q f g)) :
    (baseChangeHomeomorph q f g).symm (baseChangeHomeomorph q f g x) = x :=
  (baseChangeHomeomorph q f g).symm_apply_apply x
example (x : BaseChangedSpace q f g) :
    baseChangeHomeomorph q f g ((baseChangeHomeomorph q f g).symm x) = x :=
  (baseChangeHomeomorph q f g).apply_symm_apply x
example (h : CubicalSubdivision.BoundaryLifting (endpoint q f)) :
    CubicalSubdivision.BoundaryLifting (endpoint (baseChangedProjection q g) (baseChangedMap q f g)) :=
  endpoint_boundaryLifting_baseChange q f g h
example (h : CubicalSubdivision.BoundaryLifting (endpoint q f)) :
    IsWeakHomotopyEquivalence (baseChangedMap q f g) := baseChangedMap_isWeakHomotopyEquivalence q f g h
example (h : CubicalSubdivision.BoundaryLifting (endpoint q f)) (x : BaseChangedSource q f g) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (baseChangedMap q f g) (x := x) rfl) :=
  (baseChangedMap_isWeakHomotopyEquivalence q f g h).homotopy_bijective x 0
example (h : CubicalSubdivision.BoundaryLifting (endpoint q f)) :
    ∀ y : BaseChangedTarget q g,∃ x : BaseChangedSource q f g,Joined (baseChangedMap q f g x) y :=
  (baseChangedMap_isWeakHomotopyEquivalence q f g h).component_surjective
example (U : Set B) (h : CubicalSubdivision.BoundaryLifting (endpoint q f)) :
    CubicalSubdivision.BoundaryLifting (endpoint (restrictedProjection q U) (restrictedMap q f U)) :=
  endpoint_boundaryLifting_restriction q f U h
example (U V : Set B) (h : CubicalSubdivision.BoundaryLifting (endpoint q f)) :
    CubicalSubdivision.BoundaryLifting (endpoint (restrictedProjection q (U ∩ V)) (restrictedMap q f (U ∩ V))) :=
  endpoint_boundaryLifting_restriction q f (U ∩ V) h
example (h : CubicalSubdivision.BoundaryLifting (endpoint q f)) :
    CubicalSubdivision.BoundaryLifting (endpoint (restrictedProjection q ∅) (restrictedMap q f ∅)) :=
  endpoint_boundaryLifting_restriction q f ∅ h
