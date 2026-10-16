/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward
public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Pushforward
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.Pushforward.Acyclic
public import Quillen.Aglib.Algebra.Homology.DerivedCategory.BoundedRightDerivedUnit

/-!
# The installed derived unit on flasque sheaves and bounded complexes

The actual injective-resolution acyclicity makes the installed bounded-below
derived direct-image unit invertible on single flasque sheaves. Propagation
through the original bounded-complex theorem handles complexes with explicit
lower and upper term bounds. No assertion for unbounded-above complexes or
derived composition is made here.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- The standard ambient derived category used by the installed unit. -/
local instance flasqueDerivedPushforwardStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The installed derived unit is invertible on every original single flasque module sheaf. -/

theorem isIso_derivedPushforwardPlusUnit_single_of_flasque {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : X.Modules) [TopCat.Presheaf.IsFlasque M.presheaf] :
    IsIso ((derivedPushforwardPlusUnit f).app (singleZeroPlus X M)) :=
  isIso_derivedPushforwardPlusUnit_single_of_resolution f M (injectiveResolution M)
    (quasiIso_pushforward_injectiveResolution_int_of_quasiIso f M (injectiveResolution M)
      (quasiIso_pushforward_injectiveResolution_of_exact f M (injectiveResolution M)
        (pushforward_injectiveResolution_exact_succ_of_flasque f M (injectiveResolution M))))

/-- A bounded complex of actual flasque terms computes its original bounded-below derived image. -/

theorem isIso_derivedPushforwardPlusUnit_of_flasque_term_bounds {X Y : Scheme.{u}}
    (f : X ⟶ Y) (K : CochainComplex.Plus X.Modules)
    (a b : ℤ) (hl : ∀ i, i < a → IsZero (K.obj.X i))
    (hu : ∀ i, b < i → IsZero (K.obj.X i))
    (hK : ∀ i, TopCat.Presheaf.IsFlasque (K.obj.X i).presheaf) :
    IsIso ((derivedPushforwardPlusUnit f).app K) := by
  apply (Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit_isIso_of_term_bounds
    K a b hl hu
  intro n
  let := hK n
  exact isIso_derivedPushforwardPlusUnit_single_of_flasque f (K.obj.X n)

end AlgebraicGeometry.Scheme.Modules
