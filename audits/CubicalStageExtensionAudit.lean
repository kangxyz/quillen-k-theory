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
example {n m r : ℕ} (F : StageFace n m r) :
    (face F.1) ⁻¹' skeletonBelow n m r = _root_.Cube.boundary (Active F.1) := face_preimage_below F
example {n m r : ℕ} (F : StageFace n m r)
    (t : {t : Active F.1 → unitInterval // t ∈ _root_.Cube.boundary (Active F.1)}) :
    (stageBoundary F t).val = face F.1 t := rfl
example (n m r : ℕ) : Topology.IsQuotientMap (stageProjection n m r) := stageProjection_isQuotientMap n m r
example (n m : ℕ) : Function.Surjective (stageProjection n m 0) := stageProjection_surjective n m 0
example (n m r : ℕ) {X : Type u} [TopologicalSpace X]
    (a : C(skeletonBelow n m r,X)) (f : ∀ F : StageFace n m r,C((Active F.1 → unitInterval),X))
    (hf : ∀ F (t : {t : Active F.1 → unitInterval // t ∈ _root_.Cube.boundary (Active F.1)}),
      f F t = a (stageBoundary F t)) :
    ∃ g : C(skeleton n m r,X),
      (∀ x : skeletonBelow n m r,g ⟨x.1,skeletonBelow_subset n m r x.2⟩ = a x) ∧
      ∀ (F : StageFace n m r) (t : Active F.1 → unitInterval),
        g ⟨face F.1 t,Set.mem_iUnion.mpr ⟨⟨F.1,F.2.le⟩,⟨t,rfl⟩⟩⟩ = f F t :=
  exists_stage_paste n m r a f hf
example {n m : ℕ} (F : FaceIndex n m) (t : FaceCube.{u} F) (j : Fin (faceDimension F)) :
    (faceCubeHomeomorph F t).down j = t.down ((activeEquivFin F).symm j) := rfl
example {n m : ℕ} (F : FaceIndex n m) (t : FaceCube.{u} F) :
    (faceCubeHomeomorph F t).down ∈ _root_.Cube.boundary (Fin (faceDimension F)) ↔
      t.down ∈ _root_.Cube.boundary (Active F) := faceCubeHomeomorph_boundary_iff F t
example {n m : ℕ} (F : FaceIndex n m) : CompactSpace (FaceCubeBoundary.{u} F) := inferInstance
example {n m : ℕ} (F : FaceIndex n m) :
    TheoremA.homotopyExtensionProperty (faceBoundaryInclusion.{u} F) := faceBoundaryInclusion_hep F
example {n m : ℕ} (F : FaceIndex n m) :
    (TopCat.isoOfHomeo (faceCubeBoundaryHomeomorph.{u} F)).hom ≫
      CubicalTests.boundaryInclusion (faceDimension F) ≫
      (TopCat.isoOfHomeo (faceCubeHomeomorph.{u} F)).inv = faceBoundaryInclusion F :=
  faceBoundaryInclusion_factorization F
example {n m : ℕ} (F : FaceIndex n m) (z : FaceCubeBoundary.{u} F) :
    (faceBoundaryUnliftedHomeomorph F z).val = z.val.down := rfl
example {n m : ℕ} (F : FaceIndex n m) (h : OnOuterBoundary F) (t : Active F → unitInterval) :
    face F t ∈ _root_.Cube.boundary (Fin n) := face_mem_outerBoundary F h t
example {n m : ℕ} (F : FaceIndex n m) (h : ¬ OnOuterBoundary F) :
    (face F) ⁻¹' _root_.Cube.boundary (Fin n) ⊆ _root_.Cube.boundary (Active F) :=
  face_preimage_outerBoundary_subset F h
example {n m : ℕ} (F : FaceIndex n m) (h : OnOuterBoundary F) :
    (face F) ⁻¹' _root_.Cube.boundary (Fin n) = Set.univ := face_preimage_outerBoundary_eq_univ F h
example {n m : ℕ} (F : FaceIndex n m) : ∃ k : CellIndex n m,faceSet F ⊆ cellSet n m k :=
  faceSet_subset_cellSet F
example (n : ℕ) {X : Type u} [TopologicalSpace X] (f : C(Cube n,X)) {J : Type v}
    (U : J → Set X) (hU : ∀ j,IsOpen (U j)) (hc : ∀ x,∃ j,f x ∈ U j) :
    ∃ m,∀ F : FaceIndex n m,∃ j,∀ t : Active F → unitInterval,f (face F t) ∈ U j :=
  exists_grid_faces_subordinate n f U hU hc
