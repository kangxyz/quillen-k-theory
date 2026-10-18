/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Group.StableFieldDeterminant
public import Quillen.KTheory.Field.ElementaryProjectiveKOne

/-!
# The determinant on original projective Q K₁ over a field

The determinant is obtained by inverting the canonical quotient-to-Q composite
and then applying the proved determinant on the original elementary quotient.
Its matrix equation concerns the original completion representative. The actual
positive matrix-cube marking is proved in `Field.MatrixCubeComparison`, using
the finite-stage geometric comparison without changing this determinant.
-/
@[expose] public section

noncomputable section
universe u

namespace Quillen.FiniteProjectiveModule.StableCompletion

variable (F : Type u) [Field F]

/-- Determinant transported through the inverse of the original quotient-Q comparison. -/
def projectiveDetEquiv : (exactStructure Fᵐᵒᵖ).K 1 ≃* Fˣ :=
  (elementaryProjectiveKOneEquiv F).symm.trans (StableGeneralLinear.quotientDetEquiv F)

/-- The determinant of an original stable-completion representative. -/
theorem projectiveDetEquiv_stableGroup (g : StableGeneralLinear.Group F) :
    projectiveDetEquiv F (zeroCompletionPositiveKEquiv F 0 (stableGroupPiOneMap F g)) =
      StableGeneralLinear.det F g := by
  rw [← elementaryProjectiveKOneEquiv_quotientMap]
  exact congrArg (StableGeneralLinear.quotientDetEquiv F)
    ((elementaryProjectiveKOneEquiv F).symm_apply_apply _)

/-- On finite matrices the original completion representative has the usual determinant. -/
theorem projectiveDetEquiv_matrix (n : ℕ) (g : StableGeneralLinear.GL F n) :
    projectiveDetEquiv F
      (zeroCompletionPositiveKEquiv F 0
        (stableGroupPiOneMap F (StableGeneralLinear.of F n g))) =
      Matrix.GeneralLinearGroup.det g :=
  projectiveDetEquiv_stableGroup F _

/-- The projective determinant is natural for literal change of coefficient fields. -/
theorem projectiveDetEquiv_baseChange {L : Type u} [Field L] (f : F →+* L)
    (a : (exactStructure Fᵐᵒᵖ).K 1) :
    projectiveDetEquiv L ((rightBaseChangeExact f).KMap 1 a) =
      Units.map f.toMonoidHom (projectiveDetEquiv F a) := by
  change StableGeneralLinear.quotientDetEquiv L
    ((elementaryProjectiveKOneEquiv L).symm ((rightBaseChangeExact f).KMap 1 a)) = _
  rw [elementaryProjectiveKOneEquiv_symm_baseChange]
  exact DFunLike.congr_fun (StableGeneralLinear.quotientDetEquiv_naturality F f) _

/-- The same actual scalar-extension square, expressed as homomorphisms. -/
theorem projectiveDetEquiv_baseChange_hom {L : Type u} [Field L] (f : F →+* L) :
    (projectiveDetEquiv L).toMonoidHom.comp ((rightBaseChangeExact f).KMap 1) =
      (Units.map f.toMonoidHom).comp (projectiveDetEquiv F).toMonoidHom :=
  MonoidHom.ext (projectiveDetEquiv_baseChange F f)

end Quillen.FiniteProjectiveModule.StableCompletion
