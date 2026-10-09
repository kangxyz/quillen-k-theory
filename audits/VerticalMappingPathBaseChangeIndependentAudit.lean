import Quillen.Topology.FiberwiseMappingPath.BaseChangeLifting
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.FiberwiseMappingPath.BaseChange,
    `Quillen.Topology.FiberwiseMappingPath.BaseChangeLifting]
  let mut count : Nat := 0
  let mut counts : Array Nat := #[0,0]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    count := count + 1
    counts := counts.modify i (·+1)
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}: {axs}"
  unless counts.all (· > 0) do throwError "Missing vertical-base-change origin"
  unless count == 34 && counts == #[31,3] do throwError "Expected 34 vertical-base-change origins, found {count}"
  logInfo m!"FIXED34 PASSED {count}: {counts}"
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

-- Every original coordinate survives both directions of the homeomorphism.
example (x : Space (baseChangedProjection q g) (baseChangedMap q f g)) :
    (baseChangeHomeomorph q f g x).val.1 = x.val.1.val.1 := rfl
example (x : Space (baseChangedProjection q g) (baseChangedMap q f g)) :
    (source q f (baseChangeHomeomorph q f g x).val.2) = x.val.1.val.2 := rfl
example (x : BaseChangedSpace q f g) :
    (source (baseChangedProjection q g) (baseChangedMap q f g)
      ((baseChangeHomeomorph q f g).symm x)).val = (x.val.1,source q f x.val.2) := rfl
example (x : BaseChangedSource q f g) :
    (baseChangeHomeomorph q f g
      (inclusion (baseChangedProjection q g) (baseChangedMap q f g) x)).val =
      (x.val.1,inclusion q f x.val.2) := rfl
example (x : Space (baseChangedProjection q g) (baseChangedMap q f g)) (s : unitInterval) :
    (baseChangeHomeomorph q f g
      (contraction (baseChangedProjection q g) (baseChangedMap q f g) (s,x))).val =
      ((baseChangeHomeomorph q f g x).val.1,
        contraction q f (s,(baseChangeHomeomorph q f g x).val.2)) := rfl
example (h : CubicalSubdivision.BoundaryLifting (endpoint q f))
    (x : BaseChangedSource q f g) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (baseChangedMap q f g) (x := x) rfl) :=
  (baseChangedMap_isWeakHomotopyEquivalence q f g h).homotopy_bijective x n
example (h : CubicalSubdivision.BoundaryLifting (endpoint q f))
    [IsEmpty (BaseChangedSource q f g)] : IsEmpty (BaseChangedTarget q g) :=
  (baseChangedMap_isWeakHomotopyEquivalence q f g h).isEmpty_target
example (U : Set B) (V : Set U) (h : CubicalSubdivision.BoundaryLifting (endpoint q f)) :
    CubicalSubdivision.BoundaryLifting
      (endpoint (restrictedProjection (restrictedProjection q U) V)
        (restrictedMap (restrictedProjection q U) (restrictedMap q f U) V)) :=
  endpoint_boundaryLifting_restriction (restrictedProjection q U) (restrictedMap q f U) V
    (endpoint_boundaryLifting_restriction q f U h)
universe r
example {S : Type r} [TopologicalSpace S] (k : C(S,T))
    (h : CubicalSubdivision.BoundaryLifting (endpoint q f)) :
    CubicalSubdivision.BoundaryLifting
      (endpoint (baseChangedProjection (baseChangedProjection q g) k)
        (baseChangedMap (baseChangedProjection q g) (baseChangedMap q f g) k)) :=
  endpoint_boundaryLifting_baseChange (baseChangedProjection q g) (baseChangedMap q f g) k
    (endpoint_boundaryLifting_baseChange q f g h)
example (h : CubicalSubdivision.BoundaryLifting (endpoint q f))
    (n : ℕ) (a : C(CubicalSubdivision.Boundary n,
      Space (baseChangedProjection q g) (baseChangedMap q f g)))
    (b : C(CubicalSubdivision.Cube n,BaseChangedTarget q g))
    (hab : ∀ t,endpoint (baseChangedProjection q g) (baseChangedMap q f g) (a t) = b t.val) :
    ∃ c : C(CubicalSubdivision.Cube n,Space (baseChangedProjection q g) (baseChangedMap q f g)),
      (∀ (t : CubicalSubdivision.Boundary n) (s : unitInterval),(c t.val).val.2 s = (a t).val.2 s) ∧
      (endpoint (baseChangedProjection q g) (baseChangedMap q f g)).comp c = b := by
  obtain ⟨c,hc,hb⟩ := endpoint_boundaryLifting_baseChange q f g h n a b hab
  exact ⟨c,fun t s ↦ congrArg (fun x : Space (baseChangedProjection q g) (baseChangedMap q f g) ↦
    x.val.2 s) (hc t),hb⟩
