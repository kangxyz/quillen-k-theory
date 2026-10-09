import Quillen.Topology.CubicalSubdivision.Walls
import Quillen.Topology.CubicalSubdivision.FaceIntersections
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.CubicalSubdivision.Walls,
    `Quillen.Topology.CubicalSubdivision.FaceComplex,
    `Quillen.Topology.CubicalSubdivision.FaceBoundary,
    `Quillen.Topology.CubicalSubdivision.FaceIntersections]
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
  unless seen.size == 4 do throwError "Missing face-skeleton module origin"
  unless count == 65 do throwError "Expected 65 face-skeleton origins, found {count}"
  logInfo m!"Audited all {count} cubical face-skeleton origins."
noncomputable section
open Quillen.CubicalSubdivision
open scoped Topology unitInterval
universe u v
example (n m : ℕ) : _root_.Cube.boundary (Fin n) ⊆ walls n m := boundary_subset_walls n m
example (n m : ℕ) {X : Type u} [TopologicalSpace X]
    (a : C(walls n m,X)) (f : ∀ _k : CellIndex n m,C(Cube n,X))
    (hf : ∀ k (t : Boundary n), f k t = a (boundaryToWalls n m k t)) :
    ∃ g : C(Cube n,X), (∀ k t,g (cell n m k t) = f k t) ∧ ∀ x : walls n m,g x = a x :=
  exists_paste_from_walls n m a f hf
example (n m : ℕ) {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E,B)) (b : C(Cube n,B)) (a : C(walls n m,E))
    (f : ∀ _k : CellIndex n m,C(Cube n,E))
    (hf : ∀ k (t : Boundary n),f k t = a (boundaryToWalls n m k t))
    (hp : ∀ k,p.comp (f k) = b.comp (cell n m k)) :
    ∃ g : C(Cube n,E),p.comp g = b ∧ ∀ x : walls n m,g x = a x :=
  exists_lift_from_wall_cell_lifts n m p b a f hf hp
example {n m : ℕ} (F : FaceIndex n m) (t : Active F → unitInterval)
    (i : Fin n) (j : Fin (m+2)) (h : F i = Sum.inl j) : face F t i = gridVertex m j :=
  face_fixed F t i j h
example {n m : ℕ} (F : FaceIndex n m) (t : Active F → unitInterval)
    (i : Fin n) (k : Fin (m+1)) (h : F i = Sum.inr k) :
    face F t i = intervalCell m k (t ⟨i,k,h⟩) := face_moving F t i k h
example {n m : ℕ} (F : FaceIndex n m) : Topology.IsClosedEmbedding (face F) := face_isClosedEmbedding F
example {n m : ℕ} (F : FaceIndex n m) : faceDimension F ≤ n := faceDimension_le F
example (n m r : ℕ) : IsCompact (skeleton n m r) := skeleton_isCompact n m r
example (n m : ℕ) : skeleton n m n = Set.univ := skeleton_top n m
example (m : ℕ) : skeleton 0 m 0 = Set.univ := skeleton_top 0 m
example {n m : ℕ} (F : FaceIndex n m) (i : Active F) (j : Fin (m+2)) :
    faceDimension (fixedFace F i j) < faceDimension F := fixedFace_dimension_lt F i j
example {n m : ℕ} (F : FaceIndex n m) (t : Active F → unitInterval)
    (h : t ∈ _root_.Cube.boundary (Active F)) :
    ∃ G : FaceIndex n m,faceDimension G < faceDimension F ∧ face F t ∈ faceSet G :=
  face_boundary_lower F t h
example {n m r : ℕ} (F : FaceIndex n m) (h : faceDimension F = r+1) :
    (face F) ⁻¹' skeleton n m r = _root_.Cube.boundary (Active F) := face_preimage_skeleton F h
example {n m : ℕ} (F G : FaceIndex n m) (h : F ≠ G) (hd : faceDimension F = faceDimension G)
    (s : Active F → unitInterval) (t : Active G → unitInterval) (he : face F s = face G t) :
    s ∈ _root_.Cube.boundary (Active F) ∧ t ∈ _root_.Cube.boundary (Active G) :=
  face_intersection_boundaries F G h hd s t he
example {n m : ℕ} (F G : FaceIndex n m) (hd : faceDimension G ≤ faceDimension F)
    (s : Active F → unitInterval) (t : Active G → unitInterval)
    (hs : s ∉ _root_.Cube.boundary (Active F)) (he : face F s = face G t) : F = G :=
  face_eq_of_interior_of_dimension_le F G s t hs he hd
