/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.Pushforward.Affine
public import Quillen.Aglib.Algebra.Homology.DerivedCategory.BoundedRightDerivedUnit

/-! # The actual affine derived unit on bounded quasicoherent complexes -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The standard ambient derived category used by the actual unit. -/
local instance affineBoundedDerivedPushforwardStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

/-- On a genuinely bounded complex of quasicoherent sheaves, affine direct image computes the
original bounded-below derived direct image via its original unit. -/

theorem isIso_derivedPushforwardPlusUnit_of_term_bounds {Z X : Scheme.{u}}
    (f : Z ⟶ X) [IsAffineHom f] (K : CochainComplex.Plus Z.Modules)
    (a b : ℤ) (hl : ∀ i, i < a → IsZero (K.obj.X i))
    (hu : ∀ i, b < i → IsZero (K.obj.X i))
    (hqc : ∀ i, (K.obj.X i).IsQuasicoherent) :
    IsIso ((derivedPushforwardPlusUnit f).app K) := by
  apply (Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit_isIso_of_term_bounds
    K a b hl hu
  intro n
  let := hqc n
  exact isIso_derivedPushforwardPlusUnit_single f (K.obj.X n)

end AlgebraicGeometry.Scheme.Modules
