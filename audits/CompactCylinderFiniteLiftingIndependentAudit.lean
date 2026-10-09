import Quillen.Library
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
  let mut counts : Array Nat := targets.map fun _ ↦ 0
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some ti := targets.idxOf? origin | continue
    counts := counts.modify ti (· + 1)
    seen := seen.insert origin
    count := count + 1
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axs}"
  unless seen.size == 9 do throwError "Expected all nine defining modules"
  unless count == 47 do throwError "Expected exactly 47 defining origins, found {count}"
  logInfo m!"AUDITED {count}: {counts}"
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

/- Additional independent consumers; appended to the fixed-origin audit after source freeze. -/

section IndependentExactPieces
variable {D : Type u} [TopologicalSpace D] (b : C(D,T))
example (a : SourceStart (f := f) base b) (s : TopCat.I) :
    (parameterQuotient sq base b (.inl (a,s))).val = (l (a.val.1,s),a.val.2) := rfl
example (a : TargetStart base b) :
    (parameterQuotient sq base b (.inr a)).val = (c a.val.1,a.val.2) := rfl
example [LocallyCompactSpace D]
    (hc : IsClosed (Set.ofPred (fun z : M × D ↦ projection sq base z.1 = b z.2))) :
    Topology.IsQuotientMap (parameterQuotient sq base b) :=
  parameterQuotient_isQuotientMap sq base b hc
example (H : C(unitInterval × D,T)) (hH : ∀ d,H (0,d) = b d) :
    ∃ L : C(StartPieces (f := f) base b × unitInterval,M),
      (∀ z,L (z,0) = (parameterQuotient sq base b z).val.1) ∧
      (∀ z t,projection sq base (L (z,t)) = H (t,(parameterQuotient sq base b z).val.2)) ∧
      ∀ (a : SourceStart (f := f) base b) t,
        L (.inl (a,ULift.up 1),t) =
          L (.inr (⟨(f a.val.1,a.val.2),a.property⟩ : TargetStart base b),t) :=
  exists_piece_lift sq base b hp hq H hH
example (L : C(StartPieces (f := f) base b × unitInterval,M))
    (hcap : ∀ (a : SourceStart (f := f) base b) t,
      L (.inl (a,ULift.up 1),t) =
        L (.inr (⟨(f a.val.1,a.val.2),a.property⟩ : TargetStart base b),t)) :
    Function.FactorsThrough L (fun z ↦ (parameterQuotient sq base b z.1,z.2)) :=
  piece_lift_factorsThrough sq base b L hcap
end IndependentExactPieces

include sq base hp hq X e hf in
example (n : ℕ)
    (a : C(CubicalSubdivision.Boundary n,FiberwiseMappingPath.Space
      (projection sq base).hom (TopCat.ι₀ ≫ l).hom))
    (b : C(CubicalSubdivision.Cube n,M))
    (hw : ∀ x : CubicalSubdivision.Boundary n,
      FiberwiseMappingPath.endpoint (projection sq base).hom (TopCat.ι₀ ≫ l).hom (a x) = b x) :
    ∃ d : C(CubicalSubdivision.Cube n,FiberwiseMappingPath.Space
      (projection sq base).hom (TopCat.ι₀ ≫ l).hom),
      (∀ x : CubicalSubdivision.Boundary n,d x = a x) ∧
      (∀ (x : CubicalSubdivision.Boundary n) t,(d x).val.2 t = (a x).val.2 t) ∧
      (FiberwiseMappingPath.endpoint (projection sq base).hom (TopCat.ι₀ ≫ l).hom).comp d = b := by
  obtain ⟨d,hd,he⟩ := source_endpoint_boundaryLifting_of_realizationModel sq base hp hq X e hf n a b hw
  exact ⟨d,hd,fun x t ↦ congrArg (fun z ↦ z.val.2 t) (hd x),he⟩
example : IsWeakHomotopyEquivalence
    (FiberwiseMappingPath.endpoint (projection sq base).hom (TopCat.ι₀ ≫ l).hom) :=
  (source_endpoint_boundaryLifting_of_realizationModel sq base hp hq X e hf).isWeakHomotopyEquivalence
example (z : FiberwiseMappingPath.Space (projection sq base).hom (TopCat.ι₀ ≫ l).hom) :
    Function.Bijective (homotopyGroupMap (N := Fin 0)
      (FiberwiseMappingPath.endpoint (projection sq base).hom (TopCat.ι₀ ≫ l).hom) (x := z) rfl) :=
  ((source_endpoint_boundaryLifting_of_realizationModel sq base hp hq X e hf).isWeakHomotopyEquivalence).homotopy_bijective z 0

section IndependentDuration
variable {K D : TopCat.{u}} (i : K ⟶ D) (d : C(D,unitInterval))
  (hd : ∀ x,d x = 0 ↔ x ∈ Set.range i)
example (x : D) :
    (d x * (0 : unitInterval)) * unitInterval.symm 0 = 0 := by simp
example (x : D) :
    (d x * (1 : unitInterval)) * unitInterval.symm 1 = 0 := by simp
include hd in
example (a : K) (t : unitInterval) :
    (d (i a) * t) * unitInterval.symm t = 0 := by
  rw [(hd (i a)).mpr ⟨a,rfl⟩,zero_mul,zero_mul]
example (z : D × unitInterval) :
    (d z.1 * z.2) * unitInterval.symm z.2 = 0 ↔
      z ∈ Set.range (TheoremA.cylinderBoundaryMap i) :=
  cylinderBoundary_duration_zero_iff i d hd z
end IndependentDuration

include sq base hp hq X e hf in
private theorem original_source_weak : IsWeakHomotopyEquivalence (TopCat.ι₀ ≫ l).hom := by
  have h := (source_endpoint_boundaryLifting_of_realizationModel sq base hp hq X e hf).isWeakHomotopyEquivalence
  exact h.comp (isWeakHomotopyEquivalence_of_homotopyEquiv
    (FiberwiseMappingPath.inclusionHomotopyEquiv (projection sq base).hom (TopCat.ι₀ ≫ l).hom))
example : IsWeakHomotopyEquivalence (TopCat.ι₀ ≫ l).hom :=
  original_source_weak sq base hp hq X e hf
example (a : A) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (TopCat.ι₀ ≫ l).hom (x := a) rfl) :=
  (original_source_weak sq base hp hq X e hf).homotopy_bijective a 0
example (m : M) : ∃ a : A, Joined ((TopCat.ι₀ ≫ l) a) m :=
  (original_source_weak sq base hp hq X e hf).component_surjective m
example [IsEmpty A] : IsEmpty M :=
  (original_source_weak sq base hp hq X e hf).isEmpty_target
