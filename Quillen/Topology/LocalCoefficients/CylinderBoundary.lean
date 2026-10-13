/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.CylinderRelative

/-! # Genuine singular simplices in the two endpoint cylinder boundary -/
@[expose] public section
noncomputable section
open CategoryTheory Convexity
open scoped unitInterval
universe u
namespace Quillen.LocalCoefficients
variable (X : Type u) [TopologicalSpace X]

/-- Both closed ends of the original cylinder. -/
def cylinderBoundary : Set (unitInterval × X) := {z | z.1 ∈ ({0, 1} : Set unitInterval)}

/-- A slice regarded as a subset of the actual two-ended boundary. -/
def cylinderBoundarySlice (t : unitInterval) : Set (cylinderBoundary X) :=
  {z | z.val.1 = t}

/-- Every genuine simplex in the boundary stays in one endpoint slice. -/
theorem cylinderBoundary_simplex_small {n : SimplexCategory}
    (s : SingularSimplex (cylinderBoundary X) n) :
    IsCoverSmall (fun b : Bool => cylinderBoundarySlice X (if b then 1 else 0)) s := by
  let f : StdSimplex ℝ (Fin (n.len + 1)) →
      ({t : unitInterval // t ∈ ({0, 1} : Set unitInterval)}) :=
    fun x => ⟨(s x).val.1, (s x).property⟩
  have hf : Continuous f := by fun_prop
  have hc (x) : (s x).val.1 = (s (StdSimplex.single 0)).val.1 :=
    congrArg Subtype.val (TotallyDisconnectedSpace.eq_of_continuous f hf x (StdSimplex.single 0))
  have hp := (s (StdSimplex.single 0)).property
  change (s (StdSimplex.single 0)).val.1 = 0 ∨
    (s (StdSimplex.single 0)).val.1 = 1 at hp
  rcases hp with hp | hp
  · refine ⟨false, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hc x).trans hp
  · refine ⟨true, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hc x).trans hp

omit [TopologicalSpace X] in
/-- The two endpoint slices are disjoint subsets of the original boundary. -/
theorem cylinderBoundarySlice_disjoint :
    Disjoint (cylinderBoundarySlice X 0) (cylinderBoundarySlice X 1) := by
  rw [Set.disjoint_left]
  intro z h0 h1
  exact zero_ne_one (h0.symm.trans h1)

end Quillen.LocalCoefficients
