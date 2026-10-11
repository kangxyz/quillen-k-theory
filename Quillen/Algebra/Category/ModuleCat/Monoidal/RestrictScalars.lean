/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
/-!
# Scalar restriction tensor comparison

The original lax-monoidal scalar-restriction tensor map is invertible along a ring equivalence.
Its existing pure-tensor formula is unchanged.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor
universe u
namespace ModuleCat
variable {R S : Type u} [CommRing R] [CommRing S]
/-- The original scalar restriction tensor map is invertible along a ring equivalence. -/
instance isIso_restrictScalars_tensor (e : R ≃+* S) (M N : ModuleCat.{u} S) :
    IsIso (LaxMonoidal.μ (restrictScalars e.toRingHom) M N) := by
  change IsIso ((extendRestrictScalarsAdj e.toRingHom).homEquiv _ _
    (OplaxMonoidal.δ (extendScalars e.toRingHom) _ _ ≫
      ((extendRestrictScalarsAdj e.toRingHom).counit.app M ⊗ₘ
        (extendRestrictScalarsAdj e.toRingHom).counit.app N)))
  rw [Adjunction.homEquiv_unit]
  infer_instance
end ModuleCat
