/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarWeakComposition
public import Quillen.Waldhausen.GrothendieckComparison.WeakObjectCompositionBased

/-!
# The prescribed scalar composition cube with its original fine projection

The actual nerve triangle interpolates between the cofibration square followed by the image
of the original fine projection square and the original scalar square. Comparison, nerve and
object-loop coordinates remain independent. The final localization boundary comparison is
separate from this prescribed continuous family.
-/
@[expose] public section

open Quillen.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Convexity unitInterval
open Quillen.Waldhausen.Fibration
open scoped Simplicial Topology
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q) (K : Perfect X)

/-- The actual scalar factorization evaluated on its specified nerve composition homotopy. -/
def perfectScalarWeakCompositionCube :
    C(unitInterval × (unitInterval × unitInterval), (perfectOpenNested j).coarse.Delooping) :=
  (perfectOpenNested j).coarse.weakObjectCompositionCube
    (perfectScalarInclusion X r K) (perfectScalarProjection X r K)
    (perfectScalarInclusion_openWeak j r q hq K)
    ((perfectOpenNested j).le_weq _ (perfectScalarProjection_weak X r K))

/-- All three original coordinates survive the geometric specialization. -/
theorem perfectScalarWeakCompositionCube_apply (a s t : unitInterval) :
    perfectScalarWeakCompositionCube j r q hq K (a, s, t) =
      (perfectOpenNested j).coarse.weakObjectCompositionCube
        (perfectScalarInclusion X r K) (perfectScalarProjection X r K)
        (perfectScalarInclusion_openWeak j r q hq K)
        ((perfectOpenNested j).le_weq _ (perfectScalarProjection_weak X r K)) (a, s, t) := rfl

/-- The terminal comparison is the entire square of the unchanged scalar endomorphism. -/
theorem perfectScalarWeakCompositionCube_one (s t : unitInterval) :
    perfectScalarWeakCompositionCube j r q hq K (1, s, t) =
      bisimplexRealization (perfectOpenNested j).coarse
        ((perfectOpenNested j).coarse.weakObjectSimplex ((perfectGlobalScalar X r).app K)
          (perfectGlobalScalar_openWeak j r q hq K)).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr
          ((perfectOpenNested j).coarse.weakObjectSimplex ((perfectGlobalScalar X r).app K)
            (perfectGlobalScalar_openWeak j r q hq K)).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s) := by
  unfold perfectScalarWeakCompositionCube
  rw [Structure.weakObjectCompositionCube_one]
  simp only [perfectScalarInclusion_projection]

/-- The initial comparison retains the fine projection under the original localization map. -/
theorem perfectScalarWeakCompositionCube_zero (s t : unitInterval) :
    perfectScalarWeakCompositionCube j r q hq K (0, s, t) =
      if h : (s : ℝ) ≤ 1 / 2 then
        bisimplexRealization (perfectOpenNested j).coarse
          ((perfectOpenNested j).coarse.weakObjectSimplex (perfectScalarInclusion X r K)
            (perfectScalarInclusion_openWeak j r q hq K)).val
          ((isSimplex₂_diagonal_iff _ _ _).mpr
            ((perfectOpenNested j).coarse.weakObjectSimplex (perfectScalarInclusion X r K)
              (perfectScalarInclusion_openWeak j r q hq K)).property)
          (StdSimplex.homeomorphI.symm t,
            StdSimplex.homeomorphI.symm
              ⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, h⟩⟩)
      else
        changeWeakMap (perfectOpenNested j)
          (bisimplexRealization (perfectWaldhausen X)
            ((perfectWaldhausen X).weakObjectSimplex (perfectScalarProjection X r K)
              (perfectScalarProjection_weak X r K)).val
            ((isSimplex₂_diagonal_iff _ _ _).mpr
              ((perfectWaldhausen X).weakObjectSimplex (perfectScalarProjection X r K)
                (perfectScalarProjection_weak X r K)).property)
            (StdSimplex.homeomorphI.symm t,
              StdSimplex.homeomorphI.symm
                ⟨2 * s - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, s.2.2⟩⟩)) := by
  unfold perfectScalarWeakCompositionCube
  rw [Structure.weakObjectCompositionCube_zero]
  split_ifs with h
  · rfl
  · exact (weakObjectSquare_changeWeak (perfectOpenNested j)
      (perfectScalarProjection X r K) (perfectScalarProjection_weak X r K) _ _).symm

/-- The first half is literally the terminal comparison face of the original cofiber prism. -/
theorem perfectScalarWeakCompositionCube_shared_face (s t : unitInterval)
    (h : (s : ℝ) ≤ 1 / 2) :
    perfectScalarWeakCompositionCube j r q hq K (0, s, t) =
      perfectOpenScalarCofiberCompositionCube j r q hq K
        (1, ⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, h⟩⟩, t) := by
  rw [perfectScalarWeakCompositionCube_zero, dite_eq_left h]
  unfold perfectOpenScalarCofiberCompositionCube
  rw [Structure.cofiberPrismCompositionCube_comparison_one]

/-- The original scalar composition cube is a continuous square of actual based loops. -/
def perfectScalarWeakCompositionLoops :
    C(unitInterval × unitInterval,
      Path (perfectOpenNested j).coarse.kBasepoint (perfectOpenNested j).coarse.kBasepoint) :=
  (perfectOpenNested j).coarse.weakObjectCompositionLoops
    (perfectScalarInclusion X r K) (perfectScalarProjection X r K)
    (perfectScalarInclusion_openWeak j r q hq K)
    ((perfectOpenNested j).le_weq _ (perfectScalarProjection_weak X r K))

/-- Currying preserves all three actual scalar-factorization coordinates. -/
theorem perfectScalarWeakCompositionLoops_apply (a s t : unitInterval) :
    perfectScalarWeakCompositionLoops j r q hq K (a, s) t =
      perfectScalarWeakCompositionCube j r q hq K (a, s, t) := rfl

end Quillen.PerfectComplexes
