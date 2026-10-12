/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.CylinderBoundary
public import Quillen.Topology.LocalCoefficients.SmallChainDecomposition

/-! # Exact two-summand chains on the actual cylinder boundary -/
@[expose] public section
noncomputable section
open CategoryTheory Limits Convexity
universe u
namespace Quillen.LocalCoefficients
variable (X : Type u) [TopologicalSpace X]

/-- Every boundary simplex belongs to one of the two actual endpoint families. -/
theorem cylinderBoundary_union_small (n : SimplexCategory)
    (s : SingularSimplex (cylinderBoundary X) n) :
    IsCoverSmall (unionCover (singletonCover (cylinderBoundarySlice X 0))
      (singletonCover (cylinderBoundarySlice X 1))) s := by
  obtain ⟨b, hb⟩ := cylinderBoundary_simplex_small X s
  cases b with
  | false => exact ⟨Sum.inl (), hb⟩
  | true => exact ⟨Sum.inr (), hb⟩

/-- No boundary simplex belongs to both endpoint families. -/
theorem cylinderBoundary_not_both_small (n : SimplexCategory)
    (s : SingularSimplex (cylinderBoundary X) n) :
    ¬(IsCoverSmall (singletonCover (cylinderBoundarySlice X 0)) s ∧
      IsCoverSmall (singletonCover (cylinderBoundarySlice X 1)) s) := by
  rintro ⟨⟨_, h0⟩, ⟨_, h1⟩⟩
  have a := h0 ⟨StdSimplex.single 0, rfl⟩
  have b := h1 ⟨StdSimplex.single 0, rfl⟩
  exact zero_ne_one (a.symm.trans b)

/-- Actual chains on the two-ended boundary split into their two original slice summands. -/
def cylinderBoundarySmallChainIso (A : System.{u, u} (cylinderBoundary X)) :
    smallChainComplex (singletonCover (cylinderBoundarySlice X 0)) A ⊞
      smallChainComplex (singletonCover (cylinderBoundarySlice X 1)) A ≅
    singularChainComplex A := by
  let U := singletonCover (cylinderBoundarySlice X 0)
  let V := singletonCover (cylinderBoundarySlice X 1)
  let := smallChainGluingSum_isIso_of_disjoint U V A (cylinderBoundary_not_both_small X)
  exact (asIso (smallChainGluingSum U V A)).trans
    (allSmallChainIso (unionCover U V) A (cylinderBoundary_union_small X))

/-- The splitting retains the two original summand inclusions. -/
theorem cylinderBoundarySmallChainIso_hom (A : System.{u, u} (cylinderBoundary X)) :
    (cylinderBoundarySmallChainIso X A).hom =
      biprod.desc (smallChainComplexInclusion (singletonCover (cylinderBoundarySlice X 0)) A)
        (smallChainComplexInclusion (singletonCover (cylinderBoundarySlice X 1)) A) := by
  apply biprod.hom_ext' <;>
    simp [cylinderBoundarySmallChainIso, allSmallChainIso_hom, smallChainGluingSum]

end Quillen.LocalCoefficients
