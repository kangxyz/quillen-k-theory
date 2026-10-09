import Quillen.Topology.CubicalSubdivision.LocalLifting
import Quillen.Topology.CubicalSubdivision.FiberBoundaryLifting
import Quillen.Waldhausen.Fibration.RelativeRows.CubicalLifting
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.CubicalSubdivision.BoundaryLifting,
    `Quillen.Topology.CubicalSubdivision.LocalLifting,
    `Quillen.Topology.CubicalSubdivision.FiberBoundaryLifting,
    `Quillen.Waldhausen.Fibration.RelativeRows.CubicalLifting]
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
  unless seen.size == 4 do throwError "Missing local-boundary-lifting origin"
  unless count == 15 do throwError "Expected 15 local-boundary-lifting origins, found {count}"
  logInfo m!"Audited all {count} local-boundary-lifting origins."
noncomputable section
open CategoryTheory Quillen Quillen.CubicalSubdivision
open scoped Topology unitInterval Simplicial
universe u v w
example {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E,B)) (U : Set B) (e : {e : E // p e ∈ U}) :
    restriction p U e = ⟨p e.val,e.property⟩ := rfl
example {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E,B)) {J : Type w} (U : J → Set B) (hU : ∀ j,IsOpen (U j))
    (hc : ∀ y,∃ j,y ∈ U j) (hl : ∀ j,BoundaryLifting (restriction p (U j))) :
    BoundaryLifting p := BoundaryLifting.of_open_cover p U hU hc hl
example {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E,B)) {J : Type w} (U : J → Set B) (hU : ∀ j,IsOpen (U j))
    (hc : ∀ y,∃ j,y ∈ U j) (hl : ∀ j,BoundaryLifting (restriction p (U j)))
    (n : ℕ) (a : C(Boundary n,E)) (b : C(Cube n,B)) (hab : ∀ t,p (a t) = b t) :
    ∃ c : C(Cube n,E), (∀ t : Boundary n,c t = a t) ∧ p.comp c = b :=
  BoundaryLifting.of_open_cover p U hU hc hl n a b hab
example {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E,B)) {J : Type w} (U : J → Set B) (hU : ∀ j,IsOpen (U j))
    (hc : ∀ y,∃ j,y ∈ U j) (hl : ∀ j,BoundaryLifting (restriction p (U j)))
    (a : C(Boundary 0,E)) (b : C(Cube 0,B)) (hab : ∀ t,p (a t) = b t) :
    ∃ c : C(Cube 0,E), (∀ t : Boundary 0,c t = a t) ∧ p.comp c = b :=
  BoundaryLifting.of_open_cover p U hU hc hl 0 a b hab
example {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] (p : C(E,B))
    (h : ∀ n,HasLiftingProperty (CubicalTests.boundaryInclusion.{u} n) (TopCat.ofHom p)) :
    BoundaryLifting p := boundaryLifting_of_hasLiftingProperty p h
example {n m : ℕ} (F : FaceIndex n m)
    (t : {t : Active F → unitInterval // t ∈ _root_.Cube.boundary (Active F)}) :
    (faceParamBoundaryHomeomorph F t).val = faceParamHomeomorph F t.val := rfl
example {n m : ℕ} (F : FaceIndex n m) (t : Boundary (faceDimension F)) :
    ((faceParamBoundaryHomeomorph F).symm t).val = (faceParamHomeomorph F).symm t.val := rfl
example {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E,B)} (hp : BoundaryLifting p) {n m : ℕ} (F : FaceIndex n m)
    (a : C({t : Active F → unitInterval // t ∈ _root_.Cube.boundary (Active F)},E))
    (b : C((Active F → unitInterval),B)) (h : ∀ t,p (a t) = b t) :
    ∃ c : C((Active F → unitInterval),E),
      (∀ t : {t : Active F → unitInterval // t ∈ _root_.Cube.boundary (Active F)},c t = a t) ∧
        p.comp c = b := hp.face F a b h
example {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b,CompactHomotopyExtensionLiftingProperty (HomotopyFiber.strictMapOver p q f sq b)) :
    BoundaryLifting (MappingPath.endpoint f) :=
  MappingPath.endpoint_boundaryLifting_of_fiberHELP p q f sq hp hq hf
example {E F B B' : Type u} [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace B] [TopologicalSpace B'] {p : C(E,B)} {q : C(F,B')}
    (f : C(E,F)) (v : C(B,B')) (w : q.comp f = v.comp p)
    (hf : ∀ b,CompactHomotopyExtensionLiftingProperty (HomotopyFiber.map f v w.symm b)) :
    BoundaryLifting (MappingPath.endpoint (MappingPath.strictComparison f v w)) :=
  MappingPath.strictComparison_endpoint_boundaryLifting f v w hf
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.Fibration.RelativeRows
example {C : Type u} [Category.{u} C] {V : Structure C}
    (N : NestedWeakEquivalences V) {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) :
    BoundaryLifting (MappingPath.endpoint (rowNormalizedComparison N α)) :=
  rowNormalizedComparison_endpoint_boundaryLifting N α
example {C : Type u} [Category.{u} C] {V : Structure C}
    (N : NestedWeakEquivalences V) {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n)
    (a : C(Boundary 0,MappingPath (rowNormalizedComparison N α)))
    (b : C(Cube 0,_))
    (h : ∀ t,MappingPath.endpoint (rowNormalizedComparison N α) (a t) = b t) :
    ∃ c : C(Cube 0,MappingPath (rowNormalizedComparison N α)),
      (∀ t : Boundary 0,c t = a t) ∧
        (MappingPath.endpoint (rowNormalizedComparison N α)).comp c = b :=
  rowNormalizedComparison_endpoint_boundaryLifting N α 0 a b h
