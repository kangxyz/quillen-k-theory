/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.CofiberPrismFaces

/-! # Original cofiber-prism consumers

These clients keep the original weak cofibration, its actual quotient square, the three
specified weak-arrow faces and the literal chosen-zero quotient of the identity row.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite Quillen.Waldhausen
open Quillen.Waldhausen.QuotientRows
open scoped Simplicial
universe u v
namespace Quillen.Tests.CofiberPrism
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : W.cof i) (hwi : W.weq i)
  (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q))

include hi hwi hQ in
/-- The original quotient is acyclic by gluing the specified weak cofibration. -/
theorem original_quotient_weak : W.weq (0 : W.zero ⟶ Q) :=
  cofiberTwo_quotient_weak W i q hi hwi hQ

/-- The entire two-coordinate prism satisfies the actual quotient-grid predicates. -/
theorem genuine_prism : IsSimplex₂ W.cof W.weq (cofiberTwoPrism W i q hi hwi hQ) :=
  cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ

/-- The source face retains the original identity weak-arrow square. -/
theorem original_source_face :
    gridMap₂ (SimplexCategory.δ (2 : Fin 3)) (𝟙 ⦋1⦌) ⋙
      cofiberTwoPrism W i q hi hwi hQ =
        (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).val :=
  W.cofiberTwoPrism_source_face i q hi hwi hQ

/-- The middle face retains the original weak cofibration, with every map unchanged. -/
theorem original_middle_face :
    gridMap₂ (SimplexCategory.δ (1 : Fin 3)) (𝟙 ⦋1⦌) ⋙
      cofiberTwoPrism W i q hi hwi hQ = (W.weakObjectSimplex i hwi).val :=
  W.cofiberTwoPrism_middle_face i q hi hwi hQ

/-- The quotient face retains the original zero-to-quotient arrow. -/
theorem original_quotient_face :
    gridMap₂ (SimplexCategory.δ (0 : Fin 3)) (𝟙 ⦋1⦌) ⋙
      cofiberTwoPrism W i q hi hwi hQ =
        (W.weakObjectSimplex (0 : W.zero ⟶ Q)
          (cofiberTwo_quotient_weak W i q hi hwi hQ)).val :=
  W.cofiberTwoPrism_quotient_face i q hi hwi hQ

/-- Original nerve time zero keeps the complete identity-cofiber row. -/
theorem original_initial_row :
    gridRestriction 0 ⋙ cofiberTwoPrism W i q hi hwi hQ =
      cofiberTwoDiagram W (𝟙 A) (0 : A ⟶ W.zero) (by simp) :=
  cofiberTwoPrism_zero W i q hi hwi hQ

/-- The actual identity-row quotient face is the specified degenerate simplex. -/
theorem original_identity_quotient :
    (sSet W.cof W.weq).δ 0
        (W.cofiberObjectSimplex (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
          (cofiberTwo_identity_square W)) =
      zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋1⦌) :=
  W.cofiberIdentitySimplex_quotient_zero

omit [HasZeroMorphisms C] in
/-- Its actual canonical object loop is literally the constant based loop. -/
theorem original_identity_quotient_loop :
    W.kZeroObjectLoop (cofiberFaceObject (A := A) (B := A) (Q := W.zero) 0) =
      Path.refl W.kBasepoint := W.kZeroObjectLoop_zero

end Quillen.Tests.CofiberPrism
