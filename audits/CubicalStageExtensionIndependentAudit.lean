import Quillen.Library
import Quillen.Topology.CubicalSubdivision.StagePasting
import Quillen.Topology.CubicalSubdivision.FaceBoundaryTopology
import Quillen.Topology.CubicalSubdivision.OuterBoundary
import Quillen.Topology.CubicalSubdivision.FaceCover
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.CubicalSubdivision.StagePasting,
    `Quillen.Topology.CubicalSubdivision.FaceBoundaryTopology,
    `Quillen.Topology.CubicalSubdivision.OuterBoundary,
    `Quillen.Topology.CubicalSubdivision.FaceCover]
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
  unless seen.size == 4 do throwError "Missing stage-extension origin"
  unless count == 72 do throwError "Expected 72 stage-extension origins, found {count}"
  logInfo m!"Audited all {count} stage-extension origins."
noncomputable section
open CategoryTheory Quillen Quillen.CubicalSubdivision
open scoped Topology unitInterval
universe u v

example (n m : ℕ) : skeletonBelow n m 0 = ∅ := skeletonBelow_zero n m
example (n m r : ℕ) : skeletonBelow n m (r+1) = skeleton n m r := skeletonBelow_succ n m r
example (n m r : ℕ) : IsCompact (skeletonBelow n m r) := skeletonBelow_isCompact n m r
example (n m r : ℕ) : StageSource n m r =
    ((skeletonBelow n m r) ⊕ Σ F : StageFace n m r,Active F.val → unitInterval) := rfl
example (n m r : ℕ) (x : skeletonBelow n m r) :
    (stageProjection n m r (Sum.inl x)).val = x.val := rfl
example (n m r : ℕ) (F : StageFace n m r) (t : Active F.val → unitInterval) :
    (stageProjection n m r (Sum.inr ⟨F,t⟩)).val = face F.val t := rfl
example (n m r : ℕ) : Function.Surjective (stageProjection n m r) := stageProjection_surjective n m r
example (n m r : ℕ) : Topology.IsQuotientMap (stageProjection n m r) :=
  stageProjection_isQuotientMap n m r
example {n m r : ℕ} (F : StageFace n m r) :
    (face F.val) ⁻¹' skeletonBelow n m r = _root_.Cube.boundary (Active F.val) :=
  face_preimage_below F
example {n m r : ℕ} (F : StageFace n m r)
    (t : {t : Active F.val → unitInterval // t ∈ _root_.Cube.boundary (Active F.val)}) :
    (stageBoundary F t).val = face F.val t := rfl
example (n m : ℕ) : IsEmpty (skeletonBelow n m 0) := ⟨fun x ↦ by
  have hx := x.property
  simp only [skeletonBelow_zero,Set.mem_empty_iff_false] at hx⟩
example {n m : ℕ} (F : StageFace n m 0) :
    IsEmpty {t : Active F.val → unitInterval // t ∈ _root_.Cube.boundary (Active F.val)} := ⟨fun t ↦ by
  obtain ⟨i,_⟩ := t.property
  have h : 0 < Fintype.card (Active F.val) := Fintype.card_pos_iff.mpr ⟨i⟩
  change 0 < faceDimension F.val at h
  have hh := F.property
  omega⟩
example (n m : ℕ) {X : Type u} [TopologicalSpace X]
    (a : C(skeletonBelow n m 0,X))
    (f : ∀ F : StageFace n m 0,C((Active F.val → unitInterval),X)) :
    ∃ g : C(skeleton n m 0,X),
      (∀ x : skeletonBelow n m 0,g ⟨x.val,skeletonBelow_subset n m 0 x.property⟩ = a x) ∧
      ∀ (F : StageFace n m 0) (t : Active F.val → unitInterval),
        g ⟨face F.val t,Set.mem_iUnion.mpr ⟨⟨F.val,F.property.le⟩,⟨t,rfl⟩⟩⟩ = f F t := by
  apply exists_stage_paste n m 0 a f
  intro F t
  obtain ⟨i,_⟩ := t.property
  have h : 0 < Fintype.card (Active F.val) := Fintype.card_pos_iff.mpr ⟨i⟩
  change 0 < faceDimension F.val at h
  have hh := F.property
  omega
example (n m r : ℕ) {X : Type u} [TopologicalSpace X]
    (a : C(skeletonBelow n m r,X))
    (f : ∀ F : StageFace n m r,C((Active F.val → unitInterval),X))
    (hf : ∀ F (t : {t : Active F.val → unitInterval // t ∈ _root_.Cube.boundary (Active F.val)}),
      f F t = a (stageBoundary F t)) :
    ∃ g : C(skeleton n m r,X),
      (∀ x : skeletonBelow n m r,g ⟨x.val,skeletonBelow_subset n m r x.property⟩ = a x) ∧
      ∀ (F : StageFace n m r) (t : Active F.val → unitInterval),
        g ⟨face F.val t,Set.mem_iUnion.mpr ⟨⟨F.val,F.property.le⟩,⟨t,rfl⟩⟩⟩ = f F t :=
  exists_stage_paste n m r a f hf
example {n m : ℕ} (F : FaceIndex n m) : CompactSpace (FaceCube.{u} F) := inferInstance
example {n m : ℕ} (F : FaceIndex n m) : CompactSpace (FaceCubeBoundary.{u} F) := inferInstance
example {n m : ℕ} (F : FaceIndex n m) (z : FaceCube.{u} F) (j : Fin (faceDimension F)) :
    (faceCubeHomeomorph F z).down j = z.down ((activeEquivFin F).symm j) := rfl
example {n m : ℕ} (F : FaceIndex n m) (z : FaceCube.{u} F) :
    (faceCubeHomeomorph F z).down ∈ _root_.Cube.boundary (Fin (faceDimension F)) ↔
      z.down ∈ _root_.Cube.boundary (Active F) := faceCubeHomeomorph_boundary_iff F z
example {n m : ℕ} (F : FaceIndex n m) (z : FaceCubeBoundary.{u} F) :
    (faceBoundaryUnliftedHomeomorph F z).val = z.val.down := rfl
example {n m : ℕ} (F : FaceIndex n m) (z : FaceCubeBoundary.{u} F) :
    faceBoundaryInclusion F z = z.val := rfl
example {n m : ℕ} (F : FaceIndex n m) :
    (TopCat.isoOfHomeo (faceCubeBoundaryHomeomorph.{u} F)).hom ≫
      CubicalTests.boundaryInclusion (faceDimension F) ≫
      (TopCat.isoOfHomeo (faceCubeHomeomorph.{u} F)).inv = faceBoundaryInclusion F :=
  faceBoundaryInclusion_factorization F
example {n m : ℕ} (F : FaceIndex n m) :
    TheoremA.homotopyExtensionProperty (faceBoundaryInclusion.{u} F) := faceBoundaryInclusion_hep F
example {n m : ℕ} (F : FaceIndex n m) (Z : TopCat.{u})
    (f : C(FaceCube.{u} F,Z)) (H : C(unitInterval × FaceCubeBoundary.{u} F,Z))
    (hzero : ∀ a, H (0,a) = f a.val) :
    ∃ K : C(unitInterval × FaceCube.{u} F,Z),
      (∀ b, K (0,b) = f b) ∧ ∀ t a, K (t,a.val) = H (t,a) :=
  TheoremA.homotopyExtensionProperty_continuous (faceBoundaryInclusion_hep F) Z f H hzero
example {n m : ℕ} (F : FaceIndex n m) (hF : OnOuterBoundary F) :
    (face F) ⁻¹' _root_.Cube.boundary (Fin n) = Set.univ := face_preimage_outerBoundary_eq_univ F hF
example {n m : ℕ} (F : FaceIndex n m) (hF : ¬ OnOuterBoundary F) :
    (face F) ⁻¹' _root_.Cube.boundary (Fin n) ⊆ _root_.Cube.boundary (Active F) :=
  face_preimage_outerBoundary_subset F hF
example (m : ℕ) (F : FaceIndex 0 m) : ¬ OnOuterBoundary F := by
  rintro ⟨i,_⟩
  exact Fin.elim0 i
example {n m : ℕ} (F : FaceIndex n m) (hF : ¬ OnOuterBoundary F)
    (t : Active F → unitInterval) (ht : t ∉ _root_.Cube.boundary (Active F)) :
    face F t ∉ _root_.Cube.boundary (Fin n) := fun hx ↦ ht (face_preimage_outerBoundary_subset F hF hx)
example {n m : ℕ} (F : FaceIndex n m) :
    ∃ k : CellIndex n m, faceSet F ⊆ cellSet n m k := faceSet_subset_cellSet F
example (n : ℕ) {X : Type u} [TopologicalSpace X] (f : C(Cube n,X))
    {J : Type v} (U : J → Set X) (hU : ∀ j, IsOpen (U j)) (hcover : ∀ x, ∃ j, f x ∈ U j) :
    ∃ m : ℕ, ∀ F : FaceIndex n m, ∃ j : J,
      ∀ t : Active F → unitInterval, f (face F t) ∈ U j :=
  exists_grid_faces_subordinate n f U hU hcover
