import Quillen.Topology.FiberwiseMappingPath.LocalFiberHELP
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.FiberwiseMappingPath.BoundaryLifting,
    `Quillen.Topology.FiberwiseMappingPath.Locality,
    `Quillen.Topology.FiberwiseMappingPath.LocalFiberHELP]
  let mut count : Nat := 0
  let mut counts : Array Nat := #[0,0,0]
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
  unless count == 8 && counts == #[3,3,2] do
    throwError "Expected fixed8 = 3+3+2, found {count}: {counts}"
  logInfo m!"FIXED8 PASSED {count}: {counts}"
noncomputable section
open CategoryTheory Quillen Quillen.FiberwiseMappingPath
open scoped Topology unitInterval
universe u v w z

section
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
example
    (q : C(F,B)) (f : C(E,F)) {A D : TopCat.{u}} (i : A ⟶ D)
    (hf : ∀ (a : C(A,E)) (b : C(D,F)) (H : (f.comp a).Homotopy (b.comp i.hom)),
      (∀ t x,q (H (t,x)) = q (b (i x))) →
      ∃ c : C(D,E),c.comp i.hom = a ∧ ∃ K : (f.comp c).Homotopy b,
        HomotopyOver (q.comp b) q K ∧ ∀ t x,K (t,i x) = H (t,x)) :
    HasLiftingProperty i (TopCat.ofHom (endpoint q f)) :=
  endpoint_hasLiftingProperty_of_pairHELP q f i hf

example
    (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b : B,CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver p q f sq b)) :
    CubicalSubdivision.BoundaryLifting (endpoint q f) :=
  endpoint_boundaryLifting_of_fiberHELP p q f sq hp hq hf

end

section
variable {E : Type u} {F : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
example (q : C(F,B)) (f : C(E,F)) (U : Set B)
    (h : CubicalSubdivision.BoundaryLifting
      (endpoint (restrictedProjection q U) (restrictedMap q f U))) :
    CubicalSubdivision.BoundaryLifting (restrictedEndpoint q f U) :=
  restrictedEndpoint_boundaryLifting q f U h

example (q : C(F,B)) (f : C(E,F))
    {J : Type z} (U : J → Set B) (hU : ∀ j,IsOpen (U j))
    (hcover : ∀ b : B,∃ j,b ∈ U j)
    (h : ∀ j,CubicalSubdivision.BoundaryLifting
      (endpoint (restrictedProjection q (U j)) (restrictedMap q f (U j)))) :
    CubicalSubdivision.BoundaryLifting (endpoint q f) :=
  endpoint_boundaryLifting_of_open_cover q f U hU hcover h

example (q : C(F,B)) (f : C(E,F))
    {J : Type z} (U : J → Set B) (hU : ∀ j,IsOpen (U j))
    (hcover : ∀ b : B,∃ j,b ∈ U j)
    (h : ∀ j,CubicalSubdivision.BoundaryLifting
      (endpoint (restrictedProjection q (U j)) (restrictedMap q f (U j)))) :
    IsWeakHomotopyEquivalence f :=
  isWeakHomotopyEquivalence_of_open_cover q f U hU hcover h

end

section
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
example (q : C(F,B)) (f : C(E,F))
    {J : Type v} (U : J → Set B) (hU : ∀ j,IsOpen (U j))
    (hcover : ∀ b : B,∃ j,b ∈ U j)
    (hp : ∀ j,HomotopyLiftingProperty (restrictedProjection (q.comp f) (U j)))
    (hq : ∀ j,HomotopyLiftingProperty (restrictedProjection q (U j)))
    (hf : ∀ (j : J) (b : U j),CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver (restrictedProjection (q.comp f) (U j))
        (restrictedProjection q (U j)) (restrictedMap q f (U j)) rfl b)) :
    CubicalSubdivision.BoundaryLifting (endpoint q f) :=
  endpoint_boundaryLifting_of_local_fiberHELP q f U hU hcover hp hq hf

example (q : C(F,B)) (f : C(E,F))
    {J : Type v} (U : J → Set B) (hU : ∀ j,IsOpen (U j))
    (hcover : ∀ b : B,∃ j,b ∈ U j)
    (hp : ∀ j,HomotopyLiftingProperty (restrictedProjection (q.comp f) (U j)))
    (hq : ∀ j,HomotopyLiftingProperty (restrictedProjection q (U j)))
    (hf : ∀ (j : J) (b : U j),CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver (restrictedProjection (q.comp f) (U j))
        (restrictedProjection q (U j)) (restrictedMap q f (U j)) rfl b)) :
    IsWeakHomotopyEquivalence f :=
  isWeakHomotopyEquivalence_of_local_fiberHELP q f U hU hcover hp hq hf

end

section IndependentOriginalRestrictions
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  (q : C(F,B)) (f : C(E,F)) (U : Set B)
example : (restrictedProjection q U).comp (restrictedMap q f U) =
    restrictedProjection (q.comp f) U := rfl
example (b : U) (x : {x : RestrictedSource q f U //
    restrictedProjection (q.comp f) U x = b}) :
    ((HomotopyFiber.strictMapOver (restrictedProjection (q.comp f) U)
      (restrictedProjection q U) (restrictedMap q f U) rfl b x).val).val = f x.val.val := rfl
example (b : U) (x : {x : RestrictedSource q f U //
    restrictedProjection (q.comp f) U x = b}) :
    q (((HomotopyFiber.strictMapOver (restrictedProjection (q.comp f) U)
      (restrictedProjection q U) (restrictedMap q f U) rfl b x).val).val) = b.val :=
  congrArg Subtype.val x.property
end IndependentOriginalRestrictions

section IndependentCompleteWeakness
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  (q : C(F,B)) (f : C(E,F))
  {J : Type v} (U : J → Set B) (hU : ∀ j,IsOpen (U j))
  (hcover : ∀ b : B,∃ j,b ∈ U j)
  (hp : ∀ j,HomotopyLiftingProperty (restrictedProjection (q.comp f) (U j)))
  (hq : ∀ j,HomotopyLiftingProperty (restrictedProjection q (U j)))
  (hf : ∀ (j : J) (b : U j),CompactHomotopyExtensionLiftingProperty
    (HomotopyFiber.strictMapOver (restrictedProjection (q.comp f) (U j))
      (restrictedProjection q (U j)) (restrictedMap q f (U j)) rfl b))
include hU hcover hp hq hf
example (x : E) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) f (x := x) rfl) :=
  (isWeakHomotopyEquivalence_of_local_fiberHELP q f U hU hcover hp hq hf).homotopy_bijective x n
example (x : E) : Function.Bijective (homotopyGroupMap (N := Fin 0) f (x := x) rfl) :=
  (isWeakHomotopyEquivalence_of_local_fiberHELP q f U hU hcover hp hq hf).homotopy_bijective x 0
example (y : F) : ∃ x : E, Joined (f x) y :=
  (isWeakHomotopyEquivalence_of_local_fiberHELP q f U hU hcover hp hq hf).component_surjective y
example [IsEmpty E] : IsEmpty F :=
  (isWeakHomotopyEquivalence_of_local_fiberHELP q f U hU hcover hp hq hf).isEmpty_target
example : Function.Surjective (endpoint q f) :=
  (endpoint_boundaryLifting_of_local_fiberHELP q f U hU hcover hp hq hf).surjective
example (y : F) : ∃ (x : E) (γ : C(unitInterval,F)),
    γ 0 = f x ∧ γ 1 = y ∧ ∀ t,q (γ t) = q y := by
  obtain ⟨z,hz⟩ :=
    (endpoint_boundaryLifting_of_local_fiberHELP q f U hU hcover hp hq hf).surjective y
  refine ⟨z.val.1,z.val.2,z.property.1,hz,?_⟩
  intro t
  exact (z.property.2 t).trans ((z.property.2 1).symm.trans (congrArg q hz))
example (n : ℕ) (a : C(CubicalSubdivision.Boundary n,Space q f))
    (b : C(CubicalSubdivision.Cube n,F)) (hab : ∀ t,endpoint q f (a t) = b t.val) :
    ∃ c : C(CubicalSubdivision.Cube n,Space q f),
      (∀ t : CubicalSubdivision.Boundary n,source q f (c t.val) = source q f (a t)) ∧
      (∀ (t : CubicalSubdivision.Boundary n) (s : unitInterval),(c t.val).val.2 s = (a t).val.2 s) ∧
      (endpoint q f).comp c = b := by
  obtain ⟨c,hc,hb⟩ :=
    endpoint_boundaryLifting_of_local_fiberHELP q f U hU hcover hp hq hf n a b hab
  exact ⟨c,fun t ↦ congrArg (source q f) (hc t),
    fun t s ↦ congrArg (fun z : Space q f ↦ z.val.2 s) (hc t),hb⟩
end IndependentCompleteWeakness
