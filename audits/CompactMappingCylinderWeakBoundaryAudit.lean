import Quillen.CategoryTheory.TheoremB.CompactMappingCylinderWeakBoundary
import Quillen.Topology.CubicalSubdivision.BoundaryWeakEquivalence
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.HomotopyFiber.ContractibleBaseWeak,
    `Quillen.Topology.HELP.WeakFiberCube,
    `Quillen.CategoryTheory.TheoremB.CompactMappingCylinderWeakBoundary]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless targets.contains env.header.moduleNames[index.toNat]! do continue
    count := count + 1
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axs}"
  unless count == 10 do
    throwError "Expected exactly 10 defining-module origins, found {count}"
  logInfo m!"Audited all {count} finite weak-fiber cylinder origins."
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Quillen
open Quillen.CubicalTests Quillen.TheoremB.CompactMappingCylinder
open scoped Topology unitInterval Simplicial
universe u
section General
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b : B,IsWeakHomotopyEquivalence (HomotopyFiber.strictMapOver p q f sq b))
example (b : B) (H : (ContinuousMap.id B).Homotopy (ContinuousMap.const B b)) :
    IsWeakHomotopyEquivalence f :=
  HomotopyFiber.weak_of_strictFiber_contraction p q f sq hp hq b H (hf b)
example (n : ℕ) (a : C(boundary.{u} n,E)) (b : C(cube.{u} n,F))
    (w : f.comp a = b.comp (boundaryInclusion n).hom) :
    ∃ c : C(cube.{u} n,E),c.comp (boundaryInclusion n).hom = a ∧
      Nonempty ((f.comp c).HomotopyRel b (Set.range (boundaryInclusion n))) :=
  weak_strictHELP_on_cube p q f sq hp hq n a b w (hf _)
example (n : ℕ) (a : C(boundary.{u} n,E)) (b : C(cube.{u} n,F))
    (H : (f.comp a).Homotopy (b.comp (boundaryInclusion n).hom))
    (hH : ∀ t x,q (H (t,x)) = q (b x.val)) :
    ∃ c : C(cube.{u} n,E),c.comp (boundaryInclusion n).hom = a ∧ p.comp c = q.comp b ∧
      ∃ V : (f.comp c).Homotopy b,HomotopyOver (q.comp b) q V ∧
        ∀ (t : unitInterval) (x : boundary.{u} n),V (t,x.val) = H (t,x) :=
  weak_fullHELP_on_cube_over_base p q f sq hp hq hf n a b H hH
example (a : C(boundary.{u} 0,E)) (b : C(cube.{u} 0,F))
    (H : (f.comp a).Homotopy (b.comp (boundaryInclusion 0).hom))
    (hH : ∀ t x,q (H (t,x)) = q (b x.val)) :
    ∃ c : C(cube.{u} 0,E),c.comp (boundaryInclusion 0).hom = a ∧ p.comp c = q.comp b ∧
      ∃ V : (f.comp c).Homotopy b,HomotopyOver (q.comp b) q V ∧
        ∀ (t : unitInterval) (x : boundary.{u} 0),V (t,x.val) = H (t,x) :=
  weak_fullHELP_on_cube_over_base p q f sq hp hq hf 0 a b H hH
end General
section Cylinder
variable {A C M T : TopCat.{u}} {f : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) (base : C ⟶ T)
  (hp : HomotopyLiftingProperty (f ≫ base).hom) (hq : HomotopyLiftingProperty base.hom)
  (hM : CompactHomotopyLiftingProperty (projection sq base).hom)
  (hf : ∀ t : T,IsWeakHomotopyEquivalence
    (HomotopyFiber.strictMapOver (f ≫ base).hom base.hom f.hom rfl t))
example : CubicalSubdivision.BoundaryLifting
    (FiberwiseMappingPath.endpoint (TheoremA.mappingCylinderProjection sq ≫ base).hom
      (TopCat.ι₀ ≫ l).hom) :=
  source_endpoint_boundaryLifting_of_weak_fibers sq base hp hq hM hf
example : Function.Surjective
    (FiberwiseMappingPath.endpoint (TheoremA.mappingCylinderProjection sq ≫ base).hom
      (TopCat.ι₀ ≫ l).hom) :=
  (source_endpoint_boundaryLifting_of_weak_fibers sq base hp hq hM hf).surjective
example : IsWeakHomotopyEquivalence
    (FiberwiseMappingPath.endpoint (TheoremA.mappingCylinderProjection sq ≫ base).hom
      (TopCat.ι₀ ≫ l).hom) :=
  (source_endpoint_boundaryLifting_of_weak_fibers sq base hp hq hM hf).isWeakHomotopyEquivalence
example (n : ℕ) (a : C(boundary.{u} n,A)) (b : C(cube.{u} n,M))
    (H : (((TopCat.ι₀ ≫ l).hom).comp a).Homotopy (b.comp (boundaryInclusion n).hom))
    (hH : ∀ t x,projection sq base (H (t,x)) = projection sq base (b x.val)) :
    ∃ a' : C(cube.{u} n,A),a'.comp (boundaryInclusion n).hom = a ∧
      (f ≫ base).hom.comp a' = (projection sq base).hom.comp b ∧
      ∃ V : (((TopCat.ι₀ ≫ l).hom).comp a').Homotopy b,
        HomotopyOver ((projection sq base).hom.comp b) (projection sq base).hom V ∧
          ∀ (t : unitInterval) (x : boundary.{u} n),V (t,x.val) = H (t,x) :=
  source_cube_fullHELP_of_weak_fibers sq base hp hq hM hf n a b H hH
example (X : SSet.{u}) (e : T ≃ₜ |X|) : CubicalSubdivision.BoundaryLifting
    (FiberwiseMappingPath.endpoint (projection sq base).hom (TopCat.ι₀ ≫ l).hom) :=
  source_endpoint_boundaryLifting_of_weak_fibers_realizationModel sq base hp hq X e hf
example [IsEmpty A] : IsEmpty M := by
  refine ⟨fun m ↦ ?_⟩
  obtain ⟨z,_⟩ := (source_endpoint_boundaryLifting_of_weak_fibers sq base hp hq hM hf).surjective m
  exact isEmptyElim (FiberwiseMappingPath.source (projection sq base).hom (TopCat.ι₀ ≫ l).hom z)
example (a : C(CubicalSubdivision.Boundary 0,FiberwiseMappingPath.Space
      (projection sq base).hom (TopCat.ι₀ ≫ l).hom))
    (b : C(CubicalSubdivision.Cube 0,M))
    (hw : ∀ x : CubicalSubdivision.Boundary 0,
      FiberwiseMappingPath.endpoint (projection sq base).hom (TopCat.ι₀ ≫ l).hom (a x) = b x) :
    ∃ d : C(CubicalSubdivision.Cube 0,FiberwiseMappingPath.Space
      (projection sq base).hom (TopCat.ι₀ ≫ l).hom),
      (∀ x : CubicalSubdivision.Boundary 0,d x = a x) ∧
      (FiberwiseMappingPath.endpoint (projection sq base).hom (TopCat.ι₀ ≫ l).hom).comp d = b :=
  source_endpoint_boundaryLifting_of_weak_fibers sq base hp hq hM hf 0 a b hw
end Cylinder
