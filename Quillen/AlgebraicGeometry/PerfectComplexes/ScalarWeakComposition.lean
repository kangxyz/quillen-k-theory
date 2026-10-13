/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberPrism
public import Quillen.Waldhausen.GrothendieckComparison.WeakObjectCompositionPrism
public import Quillen.Waldhausen.Fibration.BisimplexChangeWeak

/-!
# The original scalar factorization as a weak-row nerve triangle

The actual cofibration, fine weak projection and scalar composite are retained on the three
faces. The projection is also retained in the original fine realization and compared through
the unchanged localization map. This supplies prescribed geometric data for the later boundary
calculation; it does not assert the Laurent-unit boundary identity.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Convexity
open Quillen.Waldhausen Quillen.Waldhausen.Fibration
open scoped Simplicial Topology
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q) (K : Perfect X)

/-- The actual inclusion and fine weak projection determine the original coarse nerve triangle. -/
def perfectScalarWeakComposition :
    C(StdSimplex ℝ (Fin 2) × StdSimplex ℝ (Fin 3), (perfectOpenNested j).coarse.Delooping) :=
  (perfectOpenNested j).coarse.weakObjectCompositionRealization
    (perfectScalarInclusion X r K) (perfectScalarProjection X r K)
    (perfectScalarInclusion_openWeak j r q hq K)
    ((perfectOpenNested j).le_weq _ (perfectScalarProjection_weak X r K))

/-- Both original simplex coordinates are evaluated without replacing the factorization. -/
theorem perfectScalarWeakComposition_apply
    (t : StdSimplex ℝ (Fin 2)) (z : StdSimplex ℝ (Fin 3)) :
    perfectScalarWeakComposition j r q hq K (t, z) =
      (perfectOpenNested j).coarse.weakObjectCompositionRealization
        (perfectScalarInclusion X r K) (perfectScalarProjection X r K)
        (perfectScalarInclusion_openWeak j r q hq K)
        ((perfectOpenNested j).le_weq _ (perfectScalarProjection_weak X r K)) (t, z) := rfl

/-- The inclusion face is the entire square of the original inclusion arrow. -/
theorem perfectScalarWeakComposition_inclusion
    (t z : StdSimplex ℝ (Fin 2)) :
    perfectScalarWeakComposition j r q hq K (t, z.map (SimplexCategory.δ 2)) =
      bisimplexRealization (perfectOpenNested j).coarse
        ((perfectOpenNested j).coarse.weakObjectSimplex (perfectScalarInclusion X r K)
          (perfectScalarInclusion_openWeak j r q hq K)).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr
          ((perfectOpenNested j).coarse.weakObjectSimplex (perfectScalarInclusion X r K)
          (perfectScalarInclusion_openWeak j r q hq K)).property) (t, z) := by
  exact (perfectOpenNested j).coarse.weakObjectCompositionRealization_first
    (perfectScalarInclusion X r K) (perfectScalarProjection X r K)
    (perfectScalarInclusion_openWeak j r q hq K)
    ((perfectOpenNested j).le_weq _ (perfectScalarProjection_weak X r K)) t z

/-- The projection face is the entire square of the original projection arrow. -/
theorem perfectScalarWeakComposition_projection
    (t z : StdSimplex ℝ (Fin 2)) :
    perfectScalarWeakComposition j r q hq K (t, z.map (SimplexCategory.δ 0)) =
      bisimplexRealization (perfectOpenNested j).coarse
        ((perfectOpenNested j).coarse.weakObjectSimplex (perfectScalarProjection X r K)
            ((perfectOpenNested j).le_weq _ (perfectScalarProjection_weak X r K))).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr
          ((perfectOpenNested j).coarse.weakObjectSimplex (perfectScalarProjection X r K)
            ((perfectOpenNested j).le_weq _ (perfectScalarProjection_weak X r K))).property)
        (t, z) := by
  exact (perfectOpenNested j).coarse.weakObjectCompositionRealization_second
    (perfectScalarInclusion X r K) (perfectScalarProjection X r K)
    (perfectScalarInclusion_openWeak j r q hq K)
    ((perfectOpenNested j).le_weq _ (perfectScalarProjection_weak X r K)) t z

/-- The long face is the original scalar, using the actual factorization equality. -/
theorem perfectScalarWeakComposition_scalar
    (t z : StdSimplex ℝ (Fin 2)) :
    perfectScalarWeakComposition j r q hq K (t, z.map (SimplexCategory.δ 1)) =
      bisimplexRealization (perfectOpenNested j).coarse
        ((perfectOpenNested j).coarse.weakObjectSimplex ((perfectGlobalScalar X r).app K)
          (perfectGlobalScalar_openWeak j r q hq K)).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr
          ((perfectOpenNested j).coarse.weakObjectSimplex ((perfectGlobalScalar X r).app K)
          (perfectGlobalScalar_openWeak j r q hq K)).property) (t, z) := by
  unfold perfectScalarWeakComposition
  rw [Structure.weakObjectCompositionRealization_composite]
  simp only [perfectScalarInclusion_projection]

/-- The original fine projection square maps to the full prescribed coarse projection face. -/
theorem perfectScalarWeakComposition_projection_fine
    (t z : StdSimplex ℝ (Fin 2)) :
    changeWeakMap (perfectOpenNested j)
      (bisimplexRealization (perfectWaldhausen X)
        ((perfectWaldhausen X).weakObjectSimplex (perfectScalarProjection X r K)
          (perfectScalarProjection_weak X r K)).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr
          ((perfectWaldhausen X).weakObjectSimplex (perfectScalarProjection X r K)
            (perfectScalarProjection_weak X r K)).property) (t, z)) =
      perfectScalarWeakComposition j r q hq K (t, z.map (SimplexCategory.δ 0)) := by
  rw [perfectScalarWeakComposition_projection]
  exact weakObjectSquare_changeWeak (perfectOpenNested j)
    (perfectScalarProjection X r K) (perfectScalarProjection_weak X r K) t z

end Quillen.PerfectComplexes
