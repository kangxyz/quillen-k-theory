/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.CofiberPrismHomotopy

/-! # Actual continuous cofiber-prism consumers

The clients inspect all original weak-arrow boundary squares, both actual triangle time
faces and the unchanged basepoint lines, preserving independent geometric coordinates.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Convexity
open Quillen Quillen.Waldhausen Quillen.Waldhausen.QuotientRows
open scoped Simplicial Topology
universe u v
namespace Quillen.Tests.CofiberPrismRealization
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : W.cof i) (hwi : W.weq i)
  (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q))

/-- The source boundary keeps the original identity weak-arrow square at independent times. -/
theorem original_source_square (z : StdSimplex ℝ (Fin 2)) (t : unitInterval) :
    W.cofiberPrismRealization i q hi hwi hQ (z.map (SimplexCategory.δ 2), t) =
      bisimplexRealization W (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).property)
        (z, StdSimplex.homeomorphI.symm t) :=
  W.cofiberPrismRealization_source_face i q hi hwi hQ z t

/-- The middle boundary retains the complete original weak cofibration square. -/
theorem original_middle_square (z : StdSimplex ℝ (Fin 2)) (t : unitInterval) :
    W.cofiberPrismRealization i q hi hwi hQ (z.map (SimplexCategory.δ 1), t) =
      bisimplexRealization W (W.weakObjectSimplex i hwi).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr (W.weakObjectSimplex i hwi).property)
        (z, StdSimplex.homeomorphI.symm t) :=
  W.cofiberPrismRealization_middle_face i q hi hwi hQ z t

/-- The quotient boundary is the actual zero-to-quotient weak square derived by gluing. -/
theorem original_quotient_square (z : StdSimplex ℝ (Fin 2)) (t : unitInterval) :
    W.cofiberPrismRealization i q hi hwi hQ (z.map (SimplexCategory.δ 0), t) =
      bisimplexRealization W
        (W.weakObjectSimplex (0 : W.zero ⟶ Q)
          (cofiberTwo_quotient_weak W i q hi hwi hQ)).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex (0 : W.zero ⟶ Q)
            (cofiberTwo_quotient_weak W i q hi hwi hQ)).property)
        (z, StdSimplex.homeomorphI.symm t) :=
  W.cofiberPrismRealization_quotient_face i q hi hwi hQ z t

/-- Original nerve time zero gives the literal identity-cofiber triangle. -/
theorem original_zero_time (z : StdSimplex ℝ (Fin 3)) :
    W.cofiberPrismRealization i q hi hwi hQ (z, 0) =
      SSet.toTop.map (SSet.yonedaEquiv.symm
        (W.cofiberObjectSimplex (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
          (cofiberTwo_identity_square W))) ((SimplexCategory.toTopHomeo ⦋2⦌).symm z) := by
  rw [W.cofiberPrismRealization_homotopy i q hi hwi hQ]
  exact ContinuousMap.Homotopy.apply_zero _ _

/-- Original nerve time one gives the literal displayed inclusion/quotient triangle. -/
theorem original_one_time (z : StdSimplex ℝ (Fin 3)) :
    W.cofiberPrismRealization i q hi hwi hQ (z, 1) =
      SSet.toTop.map (SSet.yonedaEquiv.symm (W.cofiberObjectSimplex i q hi hQ))
        ((SimplexCategory.toTopHomeo ⦋2⦌).symm z) := by
  rw [W.cofiberPrismRealization_homotopy i q hi hwi hQ]
  exact ContinuousMap.Homotopy.apply_one _ _

/-- Each original vertex line is literally the original chosen basepoint. -/
theorem original_vertex_line (j : Fin 3) (t : unitInterval) :
    realizationSimplicialHomotopy (W.cofiberPrismHomotopy i q hi hwi hQ)
      (t, realizationPoint (X := (Δ[2] : SSet.{max u v}))
        (ULift.up (SimplexCategory.const ⦋0⦌ ⦋2⦌ j))) = W.kBasepoint :=
  W.cofiberPrismHomotopy_fixed_vertex i q hi hwi hQ j t

/-- The full barycentric family retains its original product-simplex coordinates. -/
theorem original_two_coordinates (z : StdSimplex ℝ (Fin 3)) (t : unitInterval) :
    W.cofiberPrismRealization i q hi hwi hQ (z, t) =
      SSet.toTop.map (bisimplexFamily W (cofiberTwoPrism W i q hi hwi hQ)
        (cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ))
        ((realizationProductSimplexHomeomorph 2 1).symm
          (z, StdSimplex.homeomorphI.symm t)) := rfl

end Quillen.Tests.CofiberPrismRealization
