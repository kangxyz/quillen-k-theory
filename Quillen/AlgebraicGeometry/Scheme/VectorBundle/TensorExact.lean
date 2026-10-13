/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.TensorExact
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.AffineRetract

/-!
# Exact tensor with pulled-back affine vector bundles

The actual finite-free retraction of an affine vector bundle makes its pullback
an exact tensor coefficient. No chosen retraction or affine base-change premise
is required from the caller, and the source scheme and morphism are arbitrary.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModulesOfCommRing

namespace Quillen.SchemeSheaf

variable {X Y : Scheme.{u}}

/-- Tensoring with a pulled-back affine vector bundle preserves an original short exact sequence. -/
theorem tensor_shortExact_pullback_affine_vectorBundle (R : CommRingCat.{u})
    (f : X ⟶ Spec R) (M : (Spec R).Modules) [IsFiniteLocallyFree (Spec R) M]
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj M))).ShortExact := by
  obtain ⟨I, hI, ⟨h⟩⟩ := exists_retract_finiteFree R M
  let := hI
  exact tensor_shortExact_pullback_finiteFreeRetract f h S hS

end Quillen.SchemeSheaf
