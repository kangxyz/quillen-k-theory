/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Restriction
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Genuinely local perfectness of sheaf complexes

The derived category used here is the actual Gabriel–Zisman localization at
quasi-isomorphisms. Perfectness requires, near each scheme point, an
isomorphism in that localization to a globally bounded finite locally free
complex on the neighborhood. A single global strict representative is not
required. No equivalence with a global strict-perfect category is asserted.

This file proves zero, isomorphism invariance, quasi-isomorphism invariance,
and the inclusion of strict perfect complexes. Extension closure and the
all-perfect Waldhausen instance require additional proofs.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject

universe u

namespace Quillen.PerfectComplexes

/-- The actual localization of sheaf complexes at their quasi-isomorphisms,
in the explicitly enlarged universe needed for its morphisms. -/
abbrev Derived (X : Scheme.{u}) :=
  (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)).Localization

/-- The genuine quasi-isomorphism localization functor. -/
def toDerived (X : Scheme.{u}) : Complex X ⥤ Derived X :=
  (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)).Q

instance toDerived_isLocalization (X : Scheme.{u}) :
    (toDerived X).IsLocalization (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)) := by
  unfold toDerived
  infer_instance

instance toDerived_map_isIso {X : Scheme.{u}} {K L : Complex X} (f : K ⟶ L) [QuasiIso f] :
    IsIso ((toDerived X).map f) :=
  (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)).Q_inverts f (inferInstanceAs (QuasiIso
    f))

/-- A sheaf complex is perfect when it is locally isomorphic, in the actual
quasi-isomorphism localization, to a strict perfect complex. -/
def locallyPerfect (X : Scheme.{u}) : ObjectProperty (Complex X) := fun K ↦
  ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧ ∃ P : StrictPerfect U.toScheme,
    Nonempty ((toDerived U.toScheme).obj ((restrict U.ι).obj K) ≅
      (toDerived U.toScheme).obj P.obj)

/-- The full category of genuinely locally perfect complexes. -/
abbrev Perfect (X : Scheme.{u}) := (locallyPerfect X).FullSubcategory

variable {X : Scheme.{u}}

/-- Strict perfectness implies local perfectness on every scheme. The
converse is deliberately not asserted. -/
theorem locallyPerfect_of_strictPerfect {K : Complex X} (hK : strictPerfect X K) :
    locallyPerfect X K := by
  intro x
  refine ⟨⊤, by simp, ⟨(restrict (⊤ : X.Opens).ι).obj K,
    strictPerfect_restrict _ hK⟩, ⟨Iso.refl _⟩⟩

/-- Local perfectness is preserved by actual chain isomorphisms. -/
theorem locallyPerfect_of_iso {K L : Complex X} (e : K ≅ L)
    (hK : locallyPerfect X K) : locallyPerfect X L := by
  intro x
  obtain ⟨U, hx, P, ⟨eP⟩⟩ := hK x
  exact ⟨U, hx, P, ⟨(toDerived U.toScheme).mapIso ((restrict U.ι).mapIso e.symm) ≪≫ eP⟩⟩

instance locallyPerfect_closedUnderIsomorphisms : (locallyPerfect X).IsClosedUnderIsomorphisms where
  of_iso e hK := locallyPerfect_of_iso e hK

/-- The zero complex is locally perfect. -/
instance locallyPerfect_containsZero : (locallyPerfect X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, locallyPerfect_of_strictPerfect
    (strictPerfect_of_isZero (isZero_zero _))⟩

/-- A quasi-isomorphism preserves local perfectness in both directions.
This uses actual restriction and inversion of quasi-isomorphisms. -/
theorem locallyPerfect_iff_of_quasiIso {K L : Complex X} (f : K ⟶ L) [QuasiIso f] :
    locallyPerfect X K ↔ locallyPerfect X L := by
  constructor
  · intro hK x
    obtain ⟨U, hx, P, ⟨eP⟩⟩ := hK x
    exact ⟨U, hx, P, ⟨(asIso ((toDerived U.toScheme).map ((restrict U.ι).map f))).symm ≪≫ eP⟩⟩
  · intro hL x
    obtain ⟨U, hx, P, ⟨eP⟩⟩ := hL x
    exact ⟨U, hx, P, ⟨asIso ((toDerived U.toScheme).map ((restrict U.ι).map f)) ≪≫ eP⟩⟩

/-- The fully faithful inclusion of strict perfect complexes into locally
perfect complexes. This is not asserted to be essentially surjective. -/
def strictToPerfect (X : Scheme.{u}) : StrictPerfect X ⥤ Perfect X :=
  ObjectProperty.ιOfLE (fun _ h ↦ locallyPerfect_of_strictPerfect h)

/-- The underlying sheaf complex is unchanged by this inclusion. -/
theorem strictToPerfect_comp_inclusion (X : Scheme.{u}) :
    strictToPerfect X ⋙ (locallyPerfect X).ι = (strictPerfect X).ι := rfl

end Quillen.PerfectComplexes
