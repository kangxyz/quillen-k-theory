import Quillen.Topology.HELP.BoundaryTrackCover
import Quillen.Topology.HELP.CubeBoundaryHomeomorph
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == `Quillen.Topology.HELP.BoundaryTrackCover do continue
    count := count + 1
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axs}"
  unless count == 13 do
    throwError "Expected exactly 13 defining-module origins, found {count}"
  logInfo m!"Audited all {count} whole boundary-track cover origins."
noncomputable section
open Quillen Quillen.BoundaryTrackCover
open scoped Topology unitInterval
universe u v w z
variable {A : Type u} {D : Type v} {F : Type w} {B : Type z}
  [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace F] [TopologicalSpace B]
  (i : C(A,D)) (b : C(D,F)) (H : C(unitInterval × A,F)) (q : C(F,B))
  (N : Set F) (V : Set B) (hN : IsOpen N) (hV : IsOpen V)
  (hbase : ∀ t a,q (H (t,a)) = q (b (i a)))
  (houtside : ∀ y : F,q y ∉ V → y ∈ N)
example : bad i H N = (fun x : unitInterval × A ↦ i x.2) '' (H ⁻¹' Nᶜ) := rfl
example : U0 i b H N = b ⁻¹' N \ bad i H N := rfl
example : U1 b q V = (q.comp b) ⁻¹' V := rfl
example [CompactSpace A] [T2Space D] : IsClosed (bad i H N) := isClosed_bad i H hN
example [CompactSpace A] [T2Space D] : IsOpen (U0 i b H N) := isOpen_U0 i b H hN
example : IsOpen (U1 b q V) := isOpen_U1 b q hV
example : U0 i b H N ∪ U1 b q V = Set.univ := union_eq_univ i b H q N V hbase houtside
example (d : D) (hd : d ∉ U1 b q V) : d ∈ U0 i b H N :=
  mem_U0_of_not_mem_U1 i b H q N V hbase houtside hd
example : bad i H N ⊆ U1 b q V := bad_subset_U1 i b H q N V hbase houtside
example (a : A) (ha : i a ∈ U0 i b H N) : ∀ t : unitInterval,H (t,a) ∈ N :=
  track_mem_of_mem_U0 i b H N ha
example (a : A) (ha : i a ∈ U1 b q V) : ∀ t : unitInterval,H (t,a) ∈ q ⁻¹' V :=
  track_mem_of_mem_U1 i b H q V hbase ha
example [IsEmpty A] : bad i H N = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro d hd
  obtain ⟨a,_,_⟩ := (mem_bad_iff i H N d).mp hd
  exact isEmptyElim a
example (n : ℕ) (H : C(unitInterval × CubicalTests.boundary.{u} n,F)) :
    IsClosed (bad (CubicalTests.boundaryInclusion n).hom H N) := by
  let : CompactSpace (CubicalTests.boundaryPresentation.{u} n).space :=
    (CubicalTests.boundaryPresentation n).compact
  let : CompactSpace (CubicalTests.boundary.{u} n) :=
    (CubicalTests.boundaryPresentationHomeomorph n).compactSpace
  exact isClosed_bad _ H hN
example (H : C(unitInterval × CubicalTests.boundary.{u} 0,F)) :
    IsClosed (bad (CubicalTests.boundaryInclusion 0).hom H N) := by
  let : CompactSpace (CubicalTests.boundaryPresentation.{u} 0).space :=
    (CubicalTests.boundaryPresentation 0).compact
  let : CompactSpace (CubicalTests.boundary.{u} 0) :=
    (CubicalTests.boundaryPresentationHomeomorph 0).compactSpace
  exact isClosed_bad _ H hN

section IndependentWholeTracks
example (d : D) : d ∈ U0 i b H N ↔
    b d ∈ N ∧ ∀ a : A, i a = d → ∀ t : unitInterval,H (t,a) ∈ N := by
  constructor
  · intro hd
    refine ⟨hd.1,?_⟩
    intro a ha t
    exact track_mem_of_mem_U0 i b H N (ha.symm ▸ hd) t
  · rintro ⟨hb,hH⟩
    refine ⟨hb,?_⟩
    intro hd
    obtain ⟨a,ha,t,ht⟩ := (mem_bad_iff i H N d).mp hd
    exact ht (hH a ha t)
example (d : D) (hd : d ∈ U0 (ContinuousMap.const A d) b H N) :
    ∀ (a : A) (t : unitInterval),H (t,a) ∈ N := by
  intro a t
  exact track_mem_of_mem_U0 (ContinuousMap.const A d) b H N hd t
example (a : A) (t : unitInterval) (ht : H (t,a) ∉ N) : i a ∈ U1 b q V :=
  bad_subset_U1 i b H q N V hbase houtside ⟨(t,a),ht,rfl⟩
example [CompactSpace A] (i₀ : C(A,ℝ)) (b₀ : C(ℝ,F)) :
    IsOpen (U0 i₀ b₀ H N) := isOpen_U0 i₀ b₀ H hN
example (H₀ : C(unitInterval × CubicalTests.boundary.{u} 0,F)) :
    bad (CubicalTests.boundaryInclusion 0).hom H₀ N = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro d hd
  obtain ⟨a,_,_⟩ := (mem_bad_iff (CubicalTests.boundaryInclusion 0).hom H₀ N d).mp hd
  obtain ⟨j,_⟩ := a.property
  exact Fin.elim0 j
end IndependentWholeTracks
