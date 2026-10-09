import Quillen.Topology.Realization.Homotopy
import Quillen.CategoryTheory.QConstruction.Connected
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Path-connected geometric realizations and Quillen spaces

The geometric realization is a pointwise left Kan extension in `TopCat`.
Its colimit inclusions are jointly surjective, so every point is represented
inside a standard simplex. Since each topological simplex is path-connected,
every realization point can be joined to a vertex.

Categorical connectedness therefore gives genuine path-connectedness of the
classifying space. Applied to the already proved connectedness of an exact
category's Q-construction, this supplies path-connectedness of its Quillen
space and paths from the distinguished basepoint to every point.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Convexity
open scoped Simplicial Topology unitInterval

universe u v

namespace Quillen

/-- Every point of geometric realization is represented by a point of a simplex. -/
theorem realization_exists_simplex {X : SSet.{u}} (x : |X|) :
    ∃ (n : SimplexCategory) (f : SSet.stdSimplex.obj n ⟶ X)
      (t : |SSet.stdSimplex.obj n|), SSet.toTop.map f t = x := by
  let e := SSet.stdSimplex.leftKanExtensionObjIsoColimit SimplexCategory.toTop X
  obtain ⟨j, t, ht⟩ := Concrete.colimit_exists_rep
    (CostructuredArrow.proj SSet.stdSimplex X ⋙ SimplexCategory.toTop) (e.hom x)
  refine ⟨j.left, j.hom, SSet.toTopSimplex.inv.app j.left t, ?_⟩
  have h := congrArg (fun y => e.inv y) ht
  have hx : e.inv (e.hom x) = x := by
    change (e.hom ≫ e.inv) x = x
    rw [e.hom_inv_id]
    rfl
  rw [hx] at h
  change (colimit.ι _ j ≫ e.inv) t = x at h
  change (colimit.ι _ j ≫ (SSet.stdSimplex.leftKanExtensionObjIsoColimit
    SimplexCategory.toTop X).inv) t = x at h
  rw [Functor.ι_leftKanExtensionObjIsoColimit_inv] at h
  exact h

/-- Realizations of standard simplices are path-connected. -/
instance realizationStandardSimplex_pathConnected (n : SimplexCategory) :
    PathConnectedSpace |SSet.stdSimplex.{u}.obj n| :=
  (SimplexCategory.toTopHomeo n).symm.pathConnectedSpace

/-- Each point of a realization can be joined to the image of a vertex. -/
theorem realization_joined_vertex {X : SSet.{u}} (x : |X|) :
    ∃ v : X _⦋0⦌, Joined (realizationPoint v) x := by
  obtain ⟨n, f, t, rfl⟩ := realization_exists_simplex x
  let v : (SSet.stdSimplex.obj n) _⦋0⦌ := SSet.stdSimplex.const n.len 0 _
  refine ⟨f.app _ v, ?_⟩
  rw [← realizationPoint_naturality]
  exact (PathConnectedSpace.joined (realizationPoint v) t).map (by fun_prop)

/-- Every classifying-space point lies in the path component of an object vertex. -/
theorem classifyingSpace_joined_vertex {C : Type u} [Category.{v} C]
    (x : ClassifyingSpace C) :
    ∃ c : C, Joined (classifyingSpacePoint c) x := by
  obtain ⟨v, hv⟩ := realization_joined_vertex x
  obtain ⟨c, rfl⟩ := (CategoryTheory.nerveEquiv (C := C)).symm.surjective v
  exact ⟨c, hv⟩

/-- Categorical connectedness joins all object vertices by genuine topological paths. -/
theorem classifyingSpace_joined_points {C : Type u} [Category.{v} C]
    [IsPreconnected C] (c d : C) :
    Joined (classifyingSpacePoint c) (classifyingSpacePoint d) := by
  apply Quotient.exact (s := pathSetoid (ClassifyingSpace C))
  exact constant_of_preserves_morphisms
    (fun e : C => ZerothHomotopy.mk (classifyingSpacePoint e))
    (fun _ _ f => ZerothHomotopy.sound (classifyingSpacePath f)) c d

/-- The realization of the nerve of a connected category is path-connected. -/
instance classifyingSpace_pathConnected {C : Type u} [Category.{v} C]
    [IsConnected C] : PathConnectedSpace (ClassifyingSpace C) where
  nonempty := ⟨classifyingSpacePoint (Classical.arbitrary C)⟩
  joined x y := by
    obtain ⟨c, hc⟩ := classifyingSpace_joined_vertex x
    obtain ⟨d, hd⟩ := classifyingSpace_joined_vertex y
    exact hc.symm.trans ((classifyingSpace_joined_points c d).trans hd)

/-- A path from any chosen object vertex to any point, in a connected category. -/
def classifyingSpacePathToPoint {C : Type u} [Category.{v} C]
    [IsPreconnected C] (c : C) (x : ClassifyingSpace C) :
    Path (classifyingSpacePoint c) x := by
  apply Joined.somePath
  obtain ⟨d, hd⟩ := classifyingSpace_joined_vertex x
  exact (classifyingSpace_joined_points c d).trans hd

namespace ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Quillen's space is path-connected, using the actual realization topology. -/
theorem kSpace_pathConnected : PathConnectedSpace E.KSpace := inferInstance

/-- A genuine continuous path from the zero-object basepoint to any point of
Quillen's space. This does not assert that the Q-category has an initial object. -/
def kBasepointPath (x : E.KSpace) : Path E.kBasepoint x :=
  classifyingSpacePathToPoint E.qZero x

/-- Quillen's space has only one path component. This is a statement about
π₀ of the space; Quillen K₀ is instead its first based homotopy group. -/
theorem kSpace_zerothHomotopy_subsingleton : Subsingleton (ZerothHomotopy E.KSpace) :=
  inferInstance

end ExactStructure

end Quillen
