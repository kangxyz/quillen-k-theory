import Quillen.Topology.HELP.WeakFinite
import Quillen.Topology.HELP.WeakFiniteBased
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.HELP.WeakFiniteBased,`Quillen.Topology.HELP.CubicalHorn,
    `Quillen.Topology.HELP.WeakCubeFilling,`Quillen.Topology.HELP.WeakFinite]
  let mut count : Nat := 0
  let mut counts : Array Nat := #[0,0,0,0]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let some i := targets.idxOf? env.header.moduleNames[index.toNat]! | continue
    count := count + 1
    counts := counts.modify i (· + 1)
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axs}"
  unless count == 87 && counts == #[4,66,2,15] do
    throwError "Expected 87 = 4 + 66 + 2 + 15 origins, got {count}: {counts}"
  logInfo m!"FIXED87 PASSED {count}: {counts}"
noncomputable section
open CategoryTheory Limits Topology Quillen Quillen.CubicalTests
open scoped Topology unitInterval
universe u
section Geometry
variable (n : ℕ)
example (z : Horn.{u} n) : (hornInclusion n z).val = z.val := rfl
example (x : cube.{u} n) : (topFace n x).val = (x,1) := rfl
example (x : boundary.{u} n) : (topRim n x).val = (x.val,1) := rfl
example (t : unitInterval) (z : Horn.{u} n) :
    (hornLower n (t,z)).val = (z.val.1,unitInterval.symm t*z.val.2) := rfl
example : (ContinuousMap.id (Horn.{u} n)).Homotopy (ContinuousMap.const _ (hornZero n)) :=
  hornContraction n
example : (hornZero.{u} 0).val.2 = 0 := rfl
example : Function.Surjective (Sum.elim (topFace.{u} n) (hornInclusion n)) := hornTop_surjective n
example : IsQuotientMap (Sum.elim (topFace.{u} n) (hornInclusion n)) := hornTop_isQuotientMap n
example : IsPushout (boundaryInclusion.{u} n) (topRim n) (topFace n) (hornInclusion n) :=
  hornTop_isPushout n
example : TheoremA.homotopyExtensionProperty (hornInclusion.{u} n) := hornInclusion_hep n
example (z : ProductBoundary.{u} n) : (productBoundaryHomeomorph n z).val = stepHomeomorph n z.val := rfl
example (z : boundary.{u} (n+1)) :
    ((productBoundaryHomeomorph n).symm z).val = (stepHomeomorph n).symm z.val := rfl
example : TheoremA.homotopyExtensionProperty (productBoundaryInclusion.{u} n) :=
  productBoundaryInclusion_hep n
end Geometry
section Filling
variable {X : Type u} [TopologicalSpace X]
example (n : ℕ) (hs : ∀ x : X,Subsingleton (HomotopyGroup.Pi n X x))
    (a : C(ProductBoundary.{u} n,X)) :
    ∃ c : C(cube.{u} n × unitInterval,X),c.comp (productBoundaryInclusion n).hom = a :=
  exists_extend_productBoundary n hs a
example [Nonempty X] (hs : ∀ x : X,∀ n,Subsingleton (HomotopyGroup.Pi n X x))
    (n : ℕ) (a : C(boundary.{u} n,X)) :
    ∃ c : C(cube.{u} n,X),c.comp (boundaryInclusion n).hom = a :=
  exists_extend_boundary hs n a
example [Nonempty X] (hs : ∀ x : X,∀ n,Subsingleton (HomotopyGroup.Pi n X x))
    (a : C(boundary.{u} 0,X)) :
    ∃ c : C(cube.{u} 0,X),c.comp (boundaryInclusion 0).hom = a :=
  exists_extend_boundary hs 0 a
example (n : ℕ) (a b : C(cube.{u} n,cube.{u} n)) (x : cube.{u} n)
    (hx : a x = b x) (t : unitInterval) : straightHomotopy n a b (t,x) = b x :=
  straightHomotopy_fixed n a b x hx t
end Filling
section OriginalWeakMap
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {f : C(X,Y)} (hf : IsWeakHomotopyEquivalence f)
include hf
example (n : ℕ) (x : X) (b : C(cube.{u} n,Y))
    (hb : ∀ z : boundary.{u} n,b z.val = f x) :
    ∃ c : C(cube.{u} n,X),c.comp (boundaryInclusion n).hom = ContinuousMap.const _ x ∧
      Nonempty ((f.comp c).HomotopyRel b (Set.range (boundaryInclusion n))) :=
  hf.basedCube_strictHELP n x b hb
example (n : ℕ) (x : X) (b : C(cube.{u} n,Y))
    (H : (f.comp (ContinuousMap.const (boundary.{u} n) x)).Homotopy
      (b.comp (boundaryInclusion n).hom)) :
    ∃ c : C(cube.{u} n,X),c.comp (boundaryInclusion n).hom = ContinuousMap.const _ x ∧
      ∃ K : (f.comp c).Homotopy b,∀ (t : unitInterval) (z : boundary.{u} n),
        K (t,z.val) = H (t,z) := hf.basedCube_fullHELP n x b H
example (n : ℕ) (a : C(boundary.{u} n,X)) (b : C(cube.{u} n,Y))
    (H : (f.comp a).Homotopy (b.comp (boundaryInclusion n).hom)) :
    ∃ c : C(cube.{u} n,X),c.comp (boundaryInclusion n).hom = a ∧
      ∃ K : (f.comp c).Homotopy b,∀ (t : unitInterval) (z : boundary.{u} n),
        K (t,z.val) = H (t,z) := hf.cube_fullHELP n a b H
example (a : C(boundary.{u} 0,X)) (b : C(cube.{u} 0,Y))
    (H : (f.comp a).Homotopy (b.comp (boundaryInclusion 0).hom)) :
    ∃ c : C(cube.{u} 0,X),c.comp (boundaryInclusion 0).hom = a ∧
      ∃ K : (f.comp c).Homotopy b,∀ (t : unitInterval) (z : boundary.{u} 0),
        K (t,z.val) = H (t,z) := hf.cube_fullHELP 0 a b H
example (n : ℕ) (a : C(boundary.{u} n,X)) (b : C(cube.{u} n,Y))
    (w : f.comp a = b.comp (boundaryInclusion n).hom) :
    ∃ c : C(cube.{u} n,X),c.comp (boundaryInclusion n).hom = a ∧
      Nonempty ((f.comp c).HomotopyRel b (Set.range (boundaryInclusion n))) :=
  hf.cube_strictHELP n a b w
example : CubicalSubdivision.BoundaryLifting (MappingPath.endpoint f) :=
  hf.mappingPath_endpoint_boundaryLifting
example (a : C(CubicalSubdivision.Boundary 0,MappingPath f))
    (b : C(CubicalSubdivision.Cube 0,Y))
    (hab : ∀ z : CubicalSubdivision.Boundary 0,MappingPath.endpoint f (a z) = b z) :
    ∃ c : C(CubicalSubdivision.Cube 0,MappingPath f),
      (∀ z : CubicalSubdivision.Boundary 0,c z = a z) ∧ (MappingPath.endpoint f).comp c = b :=
  hf.mappingPath_endpoint_boundaryLifting 0 a b hab
end OriginalWeakMap
