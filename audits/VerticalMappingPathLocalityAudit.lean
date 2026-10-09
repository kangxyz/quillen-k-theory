import Quillen.Topology.FiberwiseMappingPath.LocalFiberHELP
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.FiberwiseMappingPath.BoundaryLifting,
    `Quillen.Topology.FiberwiseMappingPath.Locality,
    `Quillen.Topology.FiberwiseMappingPath.LocalFiberHELP]
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
  unless seen.size == 3 do throwError "Missing vertical-locality origin"
  unless count == 8 do throwError "Expected 8 vertical-locality origins, found {count}"
  logInfo m!"Audited all {count} vertical-locality origins."
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
