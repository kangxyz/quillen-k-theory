import Quillen.CategoryTheory.TheoremB.CompactMappingCylinderBoundary
import Quillen.Topology.CubicalSubdivision.BoundaryWeakEquivalence
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.Maps.SumSubtype,
    `Quillen.CategoryTheory.TheoremB.CompactMappingCylinderParameters,
    `Quillen.CategoryTheory.TheoremB.CompactMappingCylinderTimes,
    `Quillen.CategoryTheory.TheoremB.CompactMappingCylinderLiftFormula,
    `Quillen.CategoryTheory.TheoremB.CompactMappingCylinderLiftDescent,
    `Quillen.CategoryTheory.TheoremB.CompactMappingCylinderLifting,
    `Quillen.Topology.HELP.CompactVerticalCancellation,
    `Quillen.CategoryTheory.TheoremB.CompactMappingCylinderVerticalHELP,
    `Quillen.CategoryTheory.TheoremB.CompactMappingCylinderBoundary]
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
  unless count == 47 do
    throwError "Expected exactly 47 defining-module origins, found {count}"
  logInfo m!"Audited all {count} finite mapping-cylinder lifting origins."
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Quillen
open Quillen.TheoremB.CompactMappingCylinder
open scoped Topology unitInterval Simplicial
universe u
variable {A C M T : TopCat.{u}} {f : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) (base : C ⟶ T)
  (hp : HomotopyLiftingProperty (f ≫ base).hom) (hq : HomotopyLiftingProperty base.hom)
  (X : SSet.{u}) (e : T ≃ₜ |X|)
  (hf : ∀ t : T,CompactHomotopyExtensionLiftingProperty
    (HomotopyFiber.strictMapOver (f ≫ base).hom base.hom f.hom rfl t))
example : CompactHomotopyLiftingProperty (TheoremA.mappingCylinderProjection sq ≫ base).hom :=
  compactHomotopyLiftingProperty_of_realizationModel sq base hp hq X e
example (D : Type u) [TopologicalSpace D] [CompactSpace D] [LocallyCompactSpace D]
    (a : C(D,M)) (H : C(unitInterval × D,T))
    (h₀ : ∀ d,H (0,d) = (TheoremA.mappingCylinderProjection sq ≫ base) (a d)) :
    ∃ L : C(unitInterval × D,M),(∀ d,L (0,d) = a d) ∧
      ∀ t d,(TheoremA.mappingCylinderProjection sq ≫ base) (L (t,d)) = H (t,d) :=
  compactHomotopyLiftingProperty_of_realizationModel sq base hp hq X e D a H h₀
example (D : Type u) [TopologicalSpace D] [CompactSpace D] [LocallyCompactSpace D] [IsEmpty D]
    (a : C(D,M)) (H : C(unitInterval × D,T))
    (h₀ : ∀ d,H (0,d) = (TheoremA.mappingCylinderProjection sq ≫ base) (a d)) :
    ∃ L : C(unitInterval × D,M),(∀ d,L (0,d) = a d) ∧
      ∀ t d,(TheoremA.mappingCylinderProjection sq ≫ base) (L (t,d)) = H (t,d) :=
  compactHomotopyLiftingProperty_of_realizationModel sq base hp hq X e D a H h₀
example (n : ℕ) (a : C(CubicalTests.cube.{u} n,M))
    (H : C(unitInterval × CubicalTests.cube.{u} n,T))
    (h₀ : ∀ d,H (0,d) = projection sq base (a d)) :
    ∃ L : C(unitInterval × CubicalTests.cube.{u} n,M),(∀ d,L (0,d) = a d) ∧
      ∀ t d,projection sq base (L (t,d)) = H (t,d) :=
  compactHomotopyLiftingProperty_of_realizationModel sq base hp hq X e _ a H h₀
example (a : C(CubicalTests.cube.{u} 0,M)) (H : C(unitInterval × CubicalTests.cube.{u} 0,T))
    (h₀ : ∀ d,H (0,d) = projection sq base (a d)) :
    ∃ L : C(unitInterval × CubicalTests.cube.{u} 0,M),(∀ d,L (0,d) = a d) ∧
      ∀ t d,projection sq base (L (t,d)) = H (t,d) :=
  compactHomotopyLiftingProperty_of_realizationModel sq base hp hq X e _ a H h₀
example : CubicalSubdivision.BoundaryLifting
    (FiberwiseMappingPath.endpoint (projection sq base).hom (TopCat.ι₀ ≫ l).hom) :=
  source_endpoint_boundaryLifting_of_realizationModel sq base hp hq X e hf
example : Function.Surjective
    (FiberwiseMappingPath.endpoint (projection sq base).hom (TopCat.ι₀ ≫ l).hom) :=
  (source_endpoint_boundaryLifting_of_realizationModel sq base hp hq X e hf).surjective
example (n : ℕ)
    (a : C(CubicalSubdivision.Boundary n,FiberwiseMappingPath.Space
      (projection sq base).hom (TopCat.ι₀ ≫ l).hom))
    (b : C(CubicalSubdivision.Cube n,M))
    (hw : ∀ x : CubicalSubdivision.Boundary n,
      FiberwiseMappingPath.endpoint (projection sq base).hom (TopCat.ι₀ ≫ l).hom (a x) = b x) :
    ∃ d : C(CubicalSubdivision.Cube n,FiberwiseMappingPath.Space
      (projection sq base).hom (TopCat.ι₀ ≫ l).hom),
      (∀ x : CubicalSubdivision.Boundary n,d x = a x) ∧
      (FiberwiseMappingPath.endpoint (projection sq base).hom (TopCat.ι₀ ≫ l).hom).comp d = b :=
  source_endpoint_boundaryLifting_of_realizationModel sq base hp hq X e hf n a b hw
example (K D : TopCat.{u}) [CompactSpace K] [CompactSpace D] [LocallyCompactSpace D]
    (i : K ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (d₀ : D) (HD : (ContinuousMap.id D).Homotopy (ContinuousMap.const D d₀))
    (duration : C(D,unitInterval)) (hzero : ∀ x,duration x = 0 ↔ x ∈ Set.range i)
    (a : C(K,A)) (b : C(D,M))
    (H : (((TopCat.ι₀ ≫ l).hom).comp a).Homotopy (b.comp i.hom))
    (hH : ∀ t x,projection sq base (H (t,x)) = projection sq base (b (i x))) :
    ∃ a' : C(D,A),a'.comp i.hom = a ∧
      (f ≫ base).hom.comp a' = (projection sq base).hom.comp b ∧
      ∃ V : (((TopCat.ι₀ ≫ l).hom).comp a').Homotopy b,
        HomotopyOver ((projection sq base).hom.comp b) (projection sq base).hom V ∧
          ∀ t x,V (t,i x) = H (t,x) :=
  source_fullHELP_over_contracted_test_of_realizationModel sq base hp hq X e hf
    K D i hi d₀ HD duration hzero a b H hH

-- Original quotient coordinates, including the unchanged parameter.
example (D : Type u) [TopologicalSpace D] (b : C(D,T))
    (z : SourceStart (f := f) base b) (s : TopCat.I) :
    (parameterQuotient sq base b (.inl (z,s))).1 = (l (z.1.1,s),z.1.2) := rfl
example (D : Type u) [TopologicalSpace D] (b : C(D,T))
    (z : TargetStart base b) :
    (parameterQuotient sq base b (.inr z)).1 = (c z.1.1,z.1.2) := rfl
example (hgraph : ∀ (D : Type u) [TopologicalSpace D] [CompactSpace D] [LocallyCompactSpace D]
    (b : C(D,T)),IsClosed (Set.ofPred (fun z : D × T ↦ b z.1 = z.2))) :
    CompactHomotopyLiftingProperty (TheoremA.mappingCylinderProjection sq ≫ base).hom :=
  compactHomotopyLiftingProperty_of_closedGraphs sq base hp hq hgraph
example (hM : CompactHomotopyLiftingProperty (TheoremA.mappingCylinderProjection sq ≫ base).hom) :
    CubicalSubdivision.BoundaryLifting
      (FiberwiseMappingPath.endpoint (TheoremA.mappingCylinderProjection sq ≫ base).hom
        (TopCat.ι₀ ≫ l).hom) :=
  source_endpoint_boundaryLifting sq base hp hq hM hf
