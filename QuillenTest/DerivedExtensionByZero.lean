/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.ExtensionByZero
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
/-! # Semantic consumers of actual derived extension by zero -/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace QuillenTest.DerivedExtensionByZero

open Quillen
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The original chain adjoint is recovered by the inverse derived Hom equivalence. -/
theorem original_chain_adjoint (K : CochainComplex U.Modules ℤ) (L : CochainComplex X.Modules ℤ)
    (f : K ⟶ (restrict j).obj L) :
    (extensionByZeroDerivedHomEquiv j K L).symm ((DerivedCategory.Q (C := U.Modules)).map f) =
      (DerivedCategory.Q (C := X.Modules)).map (extensionByZeroMap j f) := by
  apply (extensionByZeroDerivedHomEquiv j K L).injective
  rw [Equiv.apply_symm_apply, extensionByZeroDerivedHomEquiv_map]
  simp [extensionByZeroMap]

/-- Both directions of the literal endpoint equivalence recover arbitrary derived arrows. -/
theorem original_inverse_laws (K : CochainComplex U.Modules ℤ) (L : CochainComplex X.Modules ℤ)
    (f : (DerivedCategory.Q (C := X.Modules)).obj ((extensionByZero j).obj K) ⟶
      (DerivedCategory.Q (C := X.Modules)).obj L)
    (g : (DerivedCategory.Q (C := U.Modules)).obj K ⟶ (DerivedCategory.Q (C := U.Modules)).obj
      ((restrict j).obj L)) :
    (extensionByZeroDerivedHomEquiv j K L).symm (extensionByZeroDerivedHomEquiv j K L f) = f ∧
      extensionByZeroDerivedHomEquiv j K L ((extensionByZeroDerivedHomEquiv j K L).symm g) = g :=
  ⟨Equiv.symm_apply_apply _ _, Equiv.apply_symm_apply _ _⟩

/-- The two original derived endpoint changes commute in a single actual square. -/
theorem original_two_sided_naturality {K K' : CochainComplex U.Modules ℤ}
    {L L' : CochainComplex X.Modules ℤ}
    (a : (DerivedCategory.Q (C := U.Modules)).obj K' ⟶ (DerivedCategory.Q (C := U.Modules)).obj K)
    (f : (DerivedCategory.Q (C := X.Modules)).obj ((extensionByZero j).obj K) ⟶
      (DerivedCategory.Q (C := X.Modules)).obj L)
    (b : (DerivedCategory.Q (C := X.Modules)).obj L ⟶ (DerivedCategory.Q (C := X.Modules)).obj L') :
    extensionByZeroDerivedHomEquiv j K' L'
        (extensionByZeroDerivedHom j a ≫ f ≫ b) =
      a ≫ extensionByZeroDerivedHomEquiv j K L f ≫ restrictDerivedHom j b := by
  rw [extensionByZeroDerivedHomEquiv_precomp, extensionByZeroDerivedHomEquiv_postcomp]

/-- Every shifted extended-source map is zero if all the corresponding local maps are zero. -/
theorem original_shifted_null_detection (K : CochainComplex U.Modules ℤ)
    (L : CochainComplex X.Modules ℤ) (n : ℤ)
    (h : ∀ g : ((DerivedCategory.Q (C := U.Modules)).obj K)⟦n⟧ ⟶
      (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj L), g = 0)
    (f : ((DerivedCategory.Q (C := X.Modules)).obj ((extensionByZero j).obj K))⟦n⟧ ⟶
      (DerivedCategory.Q (C := X.Modules)).obj L) : f = 0 :=
  (extensionByZeroDerivedShiftHomEquiv_eq_zero_iff j K L n f).mp (h _)

/-- Actual derived extension is faithful on unrestricted ambient derived objects. -/
theorem original_derived_faithfulness {K L : DerivedCategory U.Modules} (f g : K ⟶ L)
    (h : (derivedExtensionByZero j).map f = (derivedExtensionByZero j).map g) : f = g :=
  (derivedExtensionByZeroFullyFaithful j).map_injective h

/-- The same localized original unit and counit satisfy the actual triangle equation. -/
theorem original_triangle_at_complex (K : CochainComplex U.Modules ℤ) :
    (derivedExtensionByZero j).map ((derivedExtensionByZeroAdjunction j).unit.app
      ((DerivedCategory.Q (C := U.Modules)).obj
      K)) ≫
      (derivedExtensionByZeroAdjunction j).counit.app
        ((derivedExtensionByZero j).obj ((DerivedCategory.Q (C := U.Modules)).obj K)) = 𝟙 _ :=
  (derivedExtensionByZeroAdjunction j).left_triangle_components _

/-- The inverse transport retains the literal original counit for arbitrary local derived maps. -/
theorem original_counit_transport (K : CochainComplex U.Modules ℤ) (L : CochainComplex X.Modules ℤ)
    (g : (DerivedCategory.Q (C := U.Modules)).obj K ⟶ (DerivedCategory.Q (C := U.Modules)).obj
      ((restrict j).obj L)) :
    (extensionByZeroDerivedHomEquiv j K L).symm g =
      extensionByZeroDerivedHom j g ≫ (DerivedCategory.Q (C := X.Modules)).map
        ((extensionByZeroAdjunction j).counit.app L)
        :=
  extensionByZeroDerivedHomEquiv_symm_eq j K L g

/-- A target change commutes with the original shifted-source equivalence at every integer. -/
theorem original_shifted_target_square (K : CochainComplex U.Modules ℤ)
    {L L' : CochainComplex X.Modules ℤ} (n : ℤ)
    (f : ((DerivedCategory.Q (C := X.Modules)).obj ((extensionByZero j).obj K))⟦n⟧ ⟶
      (DerivedCategory.Q (C := X.Modules)).obj L)
    (b : (DerivedCategory.Q (C := X.Modules)).obj L ⟶ (DerivedCategory.Q (C := X.Modules)).obj L') :
    extensionByZeroDerivedShiftHomEquiv j K L' n (f ≫ b) =
      extensionByZeroDerivedShiftHomEquiv j K L n f ≫ restrictDerivedHom j b :=
  extensionByZeroDerivedShiftHomEquiv_postcomp j K n f b

end QuillenTest.DerivedExtensionByZero
