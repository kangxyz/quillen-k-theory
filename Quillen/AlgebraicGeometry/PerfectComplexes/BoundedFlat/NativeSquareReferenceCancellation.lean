/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeSquareFiveSimplex

/-! Full binary reference cancellation under equality of the actual square factors. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.NativeSquareReferenceCancellation
variable {X Y Y' Z : Scheme.{u}}

/-- The square-reference loop leaves precisely the full source-factor transport. -/
theorem source_reference (f f' : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Y') (k k' : Y' ⟶ Z) (hf : f = f') (hk : k = k')
    (e : h ≫ k = f ≫ g) (e' : f' ≫ g = h ≫ k') :
    (((NativeSquareFiveSimplex.sourceIso h k f g e ≪≫
        BinaryNormalizationSimplex.total f g).symm ≪≫
      BinaryNormalizationSimplex.total h k) ≪≫
      eqToIso (congrArg (fun z ↦ (BinaryNormalizationSimplex.targetMap h z).functor) hk)) ≪≫
      (BinaryNormalizationSimplex.total h k').symm ≪≫
      (NativeSquareFiveSimplex.sourceIso f' g h k' e').symm ≪≫
      BinaryNormalizationSimplex.total f' g =
    eqToIso (congrArg (fun z ↦ (BinaryNormalizationSimplex.targetMap z g).functor) hf) := by
  subst f'
  subst k'
  have hs : NativeSquareFiveSimplex.sourceIso h k f g e =
      (NativeSquareFiveSimplex.sourceIso f g h k e').symm := by
    apply Iso.ext
    rfl
  rw [hs]
  simp [Iso.trans_assoc]

end Quillen.PerfectComplexes.NativeSquareReferenceCancellation
